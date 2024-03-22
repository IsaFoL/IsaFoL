theory First_Order_Type_System
  imports First_Order_Clause
begin

inductive has_type for \<F> \<V> where
  Var: "\<V> x = \<tau> \<Longrightarrow> has_type \<F> \<V> (Var x) \<tau>" |
  Fun: "\<F> f = (\<tau>s, \<tau>) \<Longrightarrow> 
    list_all2 (has_type \<F> \<V>) ts \<tau>s \<Longrightarrow>
    has_type \<F> \<V> (Fun f ts) \<tau>"

lemma right_unique_has_type: "right_unique (has_type \<F> \<V>)"
proof (rule right_uniqueI)
  fix t \<tau>\<^sub>1 \<tau>\<^sub>2
  assume "has_type \<F> \<V> t \<tau>\<^sub>1" and "has_type \<F> \<V> t \<tau>\<^sub>2"
  thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
    by (auto elim!: has_type.cases)
qed

definition well_typed_atm where
  "well_typed_atm \<F> \<V> A \<longleftrightarrow> (\<exists>\<tau>. \<forall>t \<in> set_uprod A. has_type \<F> \<V> t \<tau>)"

definition well_typed_lit where
  "well_typed_lit \<F> \<V> L \<longleftrightarrow> well_typed_atm \<F> \<V> (atm_of L)"

definition well_typed_cls where
  "well_typed_cls \<F> \<V> C \<longleftrightarrow> (\<forall>L \<in># C. well_typed_lit \<F> \<V> L)"

definition well_typed_cls_set where
  "well_typed_cls_set \<F> \<V> N \<longleftrightarrow> (\<forall>C \<in> N. well_typed_cls \<F> \<V> C)"

definition well_typed_subst where
  "well_typed_subst \<F> \<V> \<sigma> \<longleftrightarrow> (\<forall>x. has_type \<F> \<V> (\<sigma> x) (\<V> x))"

lemma well_typed_cls_add_mset: 
  "well_typed_cls \<F> \<V> (add_mset L C) \<longleftrightarrow> well_typed_lit \<F> \<V> L \<and> well_typed_cls \<F> \<V> C"
  by (simp add: well_typed_cls_def)

lemma well_typed_cls_plus: 
  "well_typed_cls \<F> \<V> (C + D) \<longleftrightarrow> well_typed_cls \<F> \<V> C \<and> well_typed_cls \<F> \<V> D"
  by (auto simp: well_typed_cls_def)

lemma well_typed_subst_term: 
  assumes well_typed_subst: "well_typed_subst \<F> \<V> \<sigma>"
  shows "has_type \<F> \<V> (t \<cdot>t \<sigma>) \<tau> \<longleftrightarrow> has_type \<F> \<V> t \<tau>"
proof(rule iffI)
  assume "has_type \<F> \<V> (t \<cdot>t \<sigma>) \<tau>"
  thus "has_type \<F> \<V> t \<tau>"
  proof(induction "t \<cdot>t \<sigma>" \<tau>  arbitrary: t rule: has_type.induct)
    case (Var x \<tau>)
    then obtain x' where t: "t = Var x'"
      by (metis subst_apply_eq_Var)

    have "has_type \<F> \<V> t (\<V> x')"
      unfolding t 
      by (simp add: has_type.Var)

    have "has_type \<F> \<V> t (\<V> x)"
      using Var well_typed_subst
      unfolding t well_typed_subst_def
      by (metis eval_term.simps(1) has_type.Var right_uniqueD right_unique_has_type)

    then have \<V>_x': "\<tau> = \<V> x'"
      using Var well_typed_subst
      unfolding well_typed_subst_def  t
      by (metis has_type.Var right_uniqueD right_unique_has_type t)

    show ?case 
      unfolding t \<V>_x'
      by (simp add: has_type.Var)
  next
    case (Fun f \<tau>s \<tau> ts)
    show ?case 
    proof(cases t)
      case (Var x)
      from Fun show ?thesis
        using  well_typed_subst 
        unfolding well_typed_subst_def Var
        by (metis (no_types, opaque_lifting) eval_term.simps(1) has_type.simps prod.sel(2) 
              term.distinct(1) term.inject(2))
    next
      case Fun\<^sub>t: Fun
      with Fun show ?thesis
        by (simp add: has_type.simps list.rel_map(1) list_all2_mono)
    qed
  qed
next
  assume "has_type \<F> \<V> t \<tau>"
  thus "has_type \<F> \<V> (t \<cdot>t \<sigma>) \<tau>"
  proof(induction t \<tau>  rule: has_type.induct)
    case Var\<^sub>t: (Var x \<tau>)
    then show ?case
    proof(cases "Var x \<cdot>t \<sigma>")
      case Var
      then show ?thesis
        using well_typed_subst
        unfolding well_typed_subst_def
        by (metis Var\<^sub>t.hyps eval_term.simps(1))        
    next
      case Fun
      then show ?thesis
        using well_typed_subst
        unfolding well_typed_subst_def
        by (metis Var\<^sub>t.hyps eval_term.simps(1))    
    qed
  next
    case (Fun f \<tau>s \<tau> ts)
    then show ?case
      using assms list_all2_mono
      unfolding well_typed_subst_def
      by (smt (verit, ccfv_SIG) eval_term.simps(2) has_type.simps list.rel_map(1))
  qed
qed

lemma well_typed_subst_atom: 
  assumes well_typed_subst: "well_typed_subst \<F> \<V> \<sigma>"
  shows "well_typed_atm \<F> \<V> (a \<cdot>a \<sigma>) \<longleftrightarrow> well_typed_atm \<F> \<V> a"
  using well_typed_subst_term[OF well_typed_subst]
  unfolding well_typed_atm_def subst_atom_def
  by(cases a) simp

lemma well_typed_subst_literal: 
  assumes well_typed_subst: "well_typed_subst \<F> \<V> \<sigma>"
  shows "well_typed_lit \<F> \<V> (l \<cdot>l \<sigma>) \<longleftrightarrow> well_typed_lit \<F> \<V> l"
  using well_typed_subst_atom[OF well_typed_subst]
  unfolding well_typed_lit_def subst_literal_def
  by(cases l) auto

lemma well_typed_subst_clause: 
  assumes well_typed_subst: "well_typed_subst \<F> \<V> \<sigma>"
  shows "well_typed_cls \<F> \<V> (c \<cdot> \<sigma>) \<longleftrightarrow> well_typed_cls \<F> \<V> c"
  using well_typed_subst_literal[OF well_typed_subst]
  unfolding well_typed_cls_def subst_clause_def
  by blast

lemma ctxt_apply_term_preserves_typing:
  assumes
    \<kappa>_type: "has_type \<F> \<V> \<kappa>\<langle>t\<rangle> \<tau>\<^sub>1" and
    t_type: "has_type \<F> \<V> t \<tau>\<^sub>2" and
    t'_type: "has_type \<F> \<V> t' \<tau>\<^sub>2"
  shows "has_type \<F> \<V> \<kappa>\<langle>t'\<rangle> \<tau>\<^sub>1"
  using \<kappa>_type
proof (induction \<kappa> arbitrary: \<tau>\<^sub>1)
  case Hole
  then show ?case
    using t_type t'_type
    using right_unique_has_type[of \<F>, THEN right_uniqueD]
    by auto
next
  case (More f ss1 \<kappa> ss2)
  have "has_type \<F> \<V> (Fun f (ss1 @ \<kappa>\<langle>t\<rangle> # ss2)) \<tau>\<^sub>1"
    using More.prems by simp
  hence "has_type \<F> \<V> (Fun f (ss1 @ \<kappa>\<langle>t'\<rangle> # ss2)) \<tau>\<^sub>1"
  proof (cases \<F> \<V> "Fun f (ss1 @ \<kappa>\<langle>t\<rangle> # ss2)" \<tau>\<^sub>1 rule: has_type.cases)
    case (Fun \<tau>s)
    show ?thesis
    proof (rule has_type.Fun)
      show "\<F> f = (\<tau>s, \<tau>\<^sub>1)"
        using \<open>\<F> f = (\<tau>s, \<tau>\<^sub>1)\<close> .
    next
      show "list_all2 (has_type \<F> \<V>) (ss1 @ \<kappa>\<langle>t'\<rangle> # ss2) \<tau>s"
        using \<open>list_all2 (has_type \<F> \<V>) (ss1 @ \<kappa>\<langle>t\<rangle> # ss2) \<tau>s\<close>
        using More.IH
        by (smt (verit, del_insts) list_all2_Cons1 list_all2_append1 list_all2_lengthD)
    qed
  qed
  thus ?case
    by simp
qed

end