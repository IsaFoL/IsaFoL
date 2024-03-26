theory First_Order_Type_System
  imports First_Order_Clause
begin

inductive has_type :: 
  "('f \<Rightarrow> 'ty list \<times> 'ty) \<Rightarrow> ('v \<Rightarrow> 'ty) \<Rightarrow> ('f,'v) term \<Rightarrow> 'ty \<Rightarrow> bool" for \<F> \<V> where
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

definition well_typed_subst' where
  "well_typed_subst' \<F> \<V> \<sigma> \<longleftrightarrow> 
    (\<forall>x. has_type \<F> \<V> (Var x) (\<V> x) \<longrightarrow> has_type \<F> \<V> (\<sigma> x) (\<V> x))"

definition well_typed_unifier where
  "well_typed_unifier \<F> \<V> t\<^sub>1 t\<^sub>2 \<upsilon> \<longleftrightarrow> 
    (\<forall>\<tau>. has_type \<F> \<V> t\<^sub>1 \<tau> \<longrightarrow> has_type \<F> \<V> t\<^sub>2 \<tau> \<longrightarrow> (\<forall>x. has_type \<F> \<V> (\<upsilon> x) (\<V> x)))"

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

definition well_typed_imgu where
  "well_typed_imgu \<F> \<V> \<sigma> terms \<equiv> 
    term_subst.is_imgu \<sigma> terms \<and> well_typed_subst \<F> \<V> \<sigma>"

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

lemma well_typed_subst'_Var: "well_typed_subst' \<F> \<V> Var"
  unfolding well_typed_subst'_def
  by simp

value "foldr (\<lambda>(x, t) \<sigma>. \<sigma> \<odot> Var(x := t)) [(x, t)] Var"


lemma Fun_arg_types:
  assumes 
    "has_type \<F> \<V> (Fun f fs) \<tau>" 
    "has_type \<F> \<V> (Fun f gs) \<tau>" 
  obtains \<tau>s where 
    "\<F> f = (\<tau>s, \<tau>)" 
    "list_all2 (has_type \<F> \<V>) fs \<tau>s"
    "list_all2 (has_type \<F> \<V>) gs \<tau>s"
  by (metis Pair_inject assms(1) assms(2) has_type.simps term.distinct(1) term.inject(2))

lemma welltyped_zip_option:
  assumes 
    "has_type \<F> \<V> (Fun f ts) \<tau>" 
    "has_type \<F> \<V> (Fun f ss) \<tau>" 
    "zip_option ts ss = Some ds" 
  shows 
    "\<forall>(a, b) \<in> set ds. \<exists>\<tau>. has_type \<F> \<V> a \<tau> \<and> has_type \<F> \<V> b \<tau>"
proof-

  obtain \<tau>s where 
    (*"\<F> f = (\<tau>s, \<tau>)" *)
    "list_all2 (has_type \<F> \<V>) ts \<tau>s"
    "list_all2 (has_type \<F> \<V>) ss \<tau>s"
    using Fun_arg_types[OF assms(1, 2)].

  with assms(3) show ?thesis
  proof(induction ts ss arbitrary: \<tau>s ds rule: zip_induct)
    case (Cons_Cons t ts s ss)
    then obtain \<tau>' \<tau>s' where \<tau>s: "\<tau>s = \<tau>' # \<tau>s'"
      by (meson list_all2_Cons1)

    from Cons_Cons(2) 
    obtain d' ds' where ds: "ds = d' # ds'"
      by auto

    
    have "zip_option ts ss = Some ds'"
      using Cons_Cons(2) 
      unfolding ds
      by fastforce

    moreover have "list_all2 (has_type \<F> \<V>) ts \<tau>s'" 
      using Cons_Cons.prems(2) \<tau>s by blast

    moreover have "list_all2 (has_type \<F> \<V>) ss \<tau>s'"
      using Cons_Cons.prems(3) \<tau>s by blast

    ultimately have "\<forall>(t, s)\<in>set ds'. \<exists>\<tau>. has_type \<F> \<V> t \<tau> \<and> has_type \<F> \<V> s \<tau>"
      using Cons_Cons.IH
      by presburger

    moreover have "\<exists>\<tau>. has_type \<F> \<V> t \<tau> \<and> has_type \<F> \<V> s \<tau>"
      using Cons_Cons.prems(2) Cons_Cons.prems(3) \<tau>s by blast
  
    ultimately show ?case
      using Cons_Cons.prems(1) ds
      by fastforce
  qed(auto)
qed

lemma welltyped_decompose':
  assumes
    "has_type \<F> \<V> (Fun f fs) \<tau>" 
    "has_type \<F> \<V> (Fun f gs) \<tau>"
    "decompose (Fun f fs) (Fun g gs) = Some ds"
  shows "\<forall>(t, t') \<in> set ds. \<exists>\<tau>. has_type \<F> \<V> t \<tau> \<and> has_type \<F> \<V> t' \<tau>"
  using assms welltyped_zip_option[OF assms(1,2)]
  by force
  
lemma welltyped_decompose:
  assumes
    "has_type \<F> \<V> f \<tau>" 
    "has_type \<F> \<V> g \<tau>"
    "decompose f g = Some ds"
  shows "\<forall>(t, t') \<in> set ds. \<exists>\<tau>. has_type \<F> \<V> t \<tau> \<and> has_type \<F> \<V> t' \<tau>"
proof-

  obtain f' fs gs where "f = Fun f' fs" "g = Fun f' gs"
    using assms(3)
    unfolding decompose_def
    by (smt (z3) option.distinct(1) prod.simps(2) rel_option_None1 term.split_sels(2))

  then show ?thesis
    using assms welltyped_decompose'
    by (metis (mono_tags, lifting))
qed
    

lemma welltyped_unify:
  assumes 
    "unify es bs = Some unifier"
    "\<forall>(t, t') \<in> set es. \<exists>\<tau>. has_type \<F> \<V> t \<tau> \<and> has_type \<F> \<V> t' \<tau>"
    "well_typed_subst \<F> \<V> (subst_of bs)"
  shows "well_typed_subst \<F> \<V> (subst_of unifier)"
  using assms
proof(induction es bs arbitrary: unifier rule: unify.induct)
  case (1 bs)
  then show ?case
    by simp
next
  case (2 f ss g ts E bs)
  then obtain \<tau> where \<tau>:
    "has_type \<F> \<V> (Fun f ss) \<tau>" 
    "has_type \<F> \<V> (Fun g ts) \<tau>"
    by auto

  obtain ds where ds: "decompose (Fun f ss) (Fun g ts) = Some ds"
    using 2(2)
    by(simp split: option.splits)

  moreover then have "unify (ds @ E) bs = Some unifier"
    using "2.prems"(1) by auto

  moreover have "\<forall>(t, t')\<in>set (ds @ E). \<exists>\<tau>. has_type \<F> \<V> t \<tau> \<and> has_type \<F> \<V> t' \<tau>"
    using welltyped_decompose[OF \<tau> ds] 2(3)
    by fastforce
   
  ultimately show ?case 
    using 2(1) 2(4)
    by blast
next
  case (3 x t E bs)
  show ?case
  proof(cases "t = Var x")
    case True
    then show ?thesis 
      using 3
      by simp
  next
    case False
    then have "unify (subst_list (subst x t) E) ((x, t) # bs) = Some unifier"
      using 3
      by(auto split: if_splits)

    moreover have 
      "\<forall>(t, t') \<in> set (subst_list (subst x t) E). \<exists>\<tau>. has_type \<F> \<V> t \<tau> \<and> has_type \<F> \<V> t' \<tau>"
      using 3(4)
      unfolding subst_def subst_list_def
      apply auto
      by (smt (verit) case_prodD fun_upd_other fun_upd_same has_type.Var right_uniqueD right_unique_has_type well_typed_subst_def well_typed_subst_term)

    moreover have "well_typed_subst \<F> \<V> (subst_of ((x, t) # bs))"
      using 3(5)
      sorry
      

    ultimately show ?thesis 
      using 3(2)[OF False _ ]  "3.prems"(1) False by force
  qed
next
  case (4 v va x E bs)
  then show ?case sorry
qed
  
lemma welltyped_unify:
  assumes "unify [(t\<^sub>1, t\<^sub>2)] [] = Some unifier"
  shows "well_typed_unifier \<F> \<V> t\<^sub>1 t\<^sub>2 (subst_of unifier)"
  using assms 
proof(induction "[(t\<^sub>1, t\<^sub>2)]" "[]:: ('a \<times> ('b, 'a) Term.term) list" rule: unify.induct)
  case (2 f ss g ts)
  then show ?case
    apply (auto split: option.splits)
    sorry
next
  case (3 x)
  then show ?case
    apply(auto simp: has_type.Var well_typed_unifier_def split: if_splits)
    sorry
next
  case (4 v va x)
  then show ?case
    apply(auto split: if_splits)
    sorry
qed
(*  case 1
  then show ?case
    unfolding well_typed_unifier_def
    using has_type.Var
    by fastforce
next
  case 2
  then show ?case
    by(simp split: option.splits)
next
  case (3 x t E bs)
  then show ?case 
  proof(cases "t = Var x")
    case True
    moreover have "unify E [] = Some bs"
      using 3(3)
      unfolding True
      by simp
      
    ultimately show ?thesis
      using 3
      by blast
  next
    case False
    moreover then have "x \<notin> vars_term t"
      using "3.prems"
      by fastforce

    moreover have "unify (subst_list (subst x t) E) [] = Some ((x, t) # bs)"
      using 3(3)
      apply(auto simp: False split: if_splits)
    proof(induction rule: unify.induct)
      case (1 bs)
      then show ?case
        apply auto
        sorry
    next
      case (2 f ss g ts E bs)
      then show ?case sorry
    next
      case (3 x t E bs)
      then show ?case sorry
    next
      case (4 v va x E bs)
      then show ?case sorry
    qed
     

    ultimately show ?thesis 
      using 3 
      sorry
  qed
next
  case (4 f ts x E bs)
  then have "x \<notin> vars_term (Fun f ts)"
    by force
   
  have "unify (subst_list (subst x (Fun f ts)) E) [] = Some ((x, Fun f ts) # bs)"
    sorry

  then show ?case
    sorry
qed*)
  
lemma welltyped_the_mgu: 
  assumes
    "the_mgu t\<^sub>1 t\<^sub>2 = \<mu>"
  shows 
   "well_typed_unifier \<F> \<V> t\<^sub>1 t\<^sub>2 \<mu>"
  using assms welltyped_unify[of t\<^sub>1 t\<^sub>2 _ \<F> \<V>]
  unfolding the_mgu_def mgu_def well_typed_unifier_def 
  by(auto simp: has_type.Var split: option.splits)
 
lemma welltyped_imgu_exists:
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes 
    unified: "term \<cdot>t \<upsilon> = term' \<cdot>t \<upsilon>"
  obtains \<mu> :: "('f, 'v) subst"
  where 
    "\<upsilon> = \<mu> \<odot> \<upsilon>" 
    "term_subst.is_imgu \<mu> {{term, term'}}"
    "well_typed_unifier \<F> \<V> term term' \<mu>"
proof
  have finite_terms: "finite {term, term'}"
    by simp

  have "term_subst.is_unifiers (the_mgu term term') {{term, term'}}"
    unfolding term_subst.is_unifiers_def
    using the_mgu_is_unifier[OF the_mgu[OF unified, THEN conjunct1]]
    by simp

  moreover have
    "\<And>\<sigma>. term_subst.is_unifiers \<sigma> {{term, term'}} \<Longrightarrow> \<sigma> = the_mgu term term' \<odot> \<sigma>"
    unfolding term_subst.is_unifiers_def
    using
      term_subst.is_unifier_iff_if_finite[OF finite_terms]
      the_mgu[of "term" _ term']
    by blast

  ultimately have is_imgu: "term_subst.is_imgu (the_mgu term term') {{term, term'}}"
    unfolding term_subst.is_imgu_def
    by blast

  show "\<upsilon> = (the_mgu term term') \<odot> \<upsilon>" 
    using the_mgu[OF unified]
    by blast

  show "term_subst.is_imgu (the_mgu term term') {{term, term'}}"
    using is_imgu
    by blast

  obtain \<mu> where \<mu>: "the_mgu term term' = \<mu>"
    using assms ex_mgu_if_subst_apply_term_eq_subst_apply_term by blast

  show "well_typed_unifier \<F> \<V> term term' (the_mgu term term')"
    using welltyped_the_mgu[OF \<mu>, of \<F> \<V>]
    unfolding \<mu>.
qed

end
