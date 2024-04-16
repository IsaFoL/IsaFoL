theory First_Order_Type_System
  imports First_Order_Clause
begin

type_synonym ('f, 'ty) fun_types = "('f \<Rightarrow> 'ty list \<times> 'ty)"
type_synonym ('v, 'ty) var_types = "('v \<Rightarrow> 'ty)"

inductive has_type :: "('f, 'ty) fun_types \<Rightarrow> ('v, 'ty) var_types \<Rightarrow> ('f,'v) term \<Rightarrow> 'ty \<Rightarrow> bool" 
  for \<F> \<V> where
  Var: "\<V> x = \<tau> \<Longrightarrow> has_type \<F> \<V> (Var x) \<tau>"
| Fun: "\<F> f = (\<tau>s, \<tau>) \<Longrightarrow> has_type \<F> \<V> (Fun f ts) \<tau>"

inductive welltyped :: "('f, 'ty) fun_types \<Rightarrow>  ('v, 'ty) var_types \<Rightarrow> ('f,'v) term \<Rightarrow> 'ty \<Rightarrow> bool" 
  for \<F> \<V> where
  Var: "\<V> x = \<tau> \<Longrightarrow> welltyped \<F> \<V> (Var x) \<tau>"
| Fun: "\<F> f = (\<tau>s, \<tau>) \<Longrightarrow> list_all2 (welltyped \<F> \<V>) ts \<tau>s \<Longrightarrow> welltyped \<F> \<V> (Fun f ts) \<tau>"

lemma has_type_right_unique: "right_unique (has_type \<F> \<V>)"
proof (rule right_uniqueI)
  fix t \<tau>\<^sub>1 \<tau>\<^sub>2
  assume "has_type \<F> \<V> t \<tau>\<^sub>1" and "has_type \<F> \<V> t \<tau>\<^sub>2"
  thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
    by (auto elim!: has_type.cases)
qed

lemma welltyped_right_unique: "right_unique (welltyped \<F> \<V>)"
proof (rule right_uniqueI)
  fix t \<tau>\<^sub>1 \<tau>\<^sub>2
  assume "welltyped \<F> \<V> t \<tau>\<^sub>1" and "welltyped \<F> \<V> t \<tau>\<^sub>2"
  thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
    by (auto elim!: welltyped.cases)
qed

definition has_type\<^sub>a where
  "has_type\<^sub>a \<F> \<V> A \<longleftrightarrow> (\<exists>\<tau>. \<forall>t \<in> set_uprod A. has_type \<F> \<V> t \<tau>)"

definition welltyped\<^sub>a where
  "welltyped\<^sub>a \<F> \<V> A \<longleftrightarrow> (\<exists>\<tau>. \<forall>t \<in> set_uprod A. welltyped \<F> \<V> t \<tau>)"

definition has_type\<^sub>l where
  "has_type\<^sub>l \<F> \<V> L \<longleftrightarrow> has_type\<^sub>a \<F> \<V> (atm_of L)"

definition welltyped\<^sub>l where
  "welltyped\<^sub>l \<F> \<V> L \<longleftrightarrow> welltyped\<^sub>a \<F> \<V> (atm_of L)"

definition has_type\<^sub>c where
  "has_type\<^sub>c \<F> \<V> C \<longleftrightarrow> (\<forall>L \<in># C. has_type\<^sub>l \<F> \<V> L)"

definition welltyped\<^sub>c where
  "welltyped\<^sub>c \<F> \<V> C \<longleftrightarrow> (\<forall>L \<in># C. welltyped\<^sub>l \<F> \<V> L)"

definition has_type\<^sub>c\<^sub>s where
  "has_type\<^sub>c\<^sub>s \<F> \<V> N \<longleftrightarrow> (\<forall>C \<in> N. has_type\<^sub>c \<F> \<V> C)"

definition welltyped\<^sub>c\<^sub>s where
  "welltyped\<^sub>c\<^sub>s \<F> \<V> N \<longleftrightarrow> (\<forall>C \<in> N. welltyped\<^sub>c \<F> \<V> C)"

(* TODO: Rename *)
definition has_type\<^sub>\<sigma> where
  "has_type\<^sub>\<sigma> \<F> \<V> \<sigma> \<longleftrightarrow> (\<forall>t \<tau>. has_type \<F> \<V> t \<tau> \<longrightarrow> has_type \<F> \<V> (t \<cdot>t \<sigma>) \<tau>)"

definition has_type\<^sub>\<sigma>' where
  "has_type\<^sub>\<sigma>' \<F> \<V> \<sigma> \<longleftrightarrow> (\<forall>x. has_type \<F> \<V> (\<sigma> x) (\<V> x))"

(* TODO: Would also (\<forall>t \<tau>. welltyped \<F> \<V> t \<tau> \<longrightarrow> welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau>)  work? *)
definition welltyped\<^sub>\<sigma> where
  "welltyped\<^sub>\<sigma> \<F> \<V> \<sigma> \<longleftrightarrow> (\<forall>x. welltyped \<F> \<V> (\<sigma> x) (\<V> x))"

lemma has_type\<^sub>c_add_mset: 
  "has_type\<^sub>c \<F> \<V> (add_mset L C) \<longleftrightarrow> has_type\<^sub>l \<F> \<V> L \<and> has_type\<^sub>c \<F> \<V> C"
  by (simp add: has_type\<^sub>c_def)

lemma welltyped\<^sub>c_add_mset: 
  "welltyped\<^sub>c \<F> \<V> (add_mset L C) \<longleftrightarrow> welltyped\<^sub>l \<F> \<V> L \<and> welltyped\<^sub>c \<F> \<V> C"
  by (simp add: welltyped\<^sub>c_def)

lemma has_type\<^sub>c_plus: 
  "has_type\<^sub>c \<F> \<V> (C + D) \<longleftrightarrow> has_type\<^sub>c \<F> \<V> C \<and> has_type\<^sub>c \<F> \<V> D"
  by (auto simp: has_type\<^sub>c_def)

lemma welltyped\<^sub>c_plus: 
  "welltyped\<^sub>c \<F> \<V> (C + D) \<longleftrightarrow> welltyped\<^sub>c \<F> \<V> C \<and> welltyped\<^sub>c \<F> \<V> D"
  by (auto simp: welltyped\<^sub>c_def)

lemma has_type\<^sub>\<sigma>_has_type: 
  assumes "has_type\<^sub>\<sigma> \<F> \<V> \<sigma>" "has_type \<F> \<V> t \<tau>"
  shows "has_type \<F> \<V> (t \<cdot>t \<sigma>) \<tau>"
  using assms 
  unfolding has_type\<^sub>\<sigma>_def
  by blast

lemma welltyped\<^sub>\<sigma>_welltyped: 
  assumes welltyped\<^sub>\<sigma>: "welltyped\<^sub>\<sigma> \<F> \<V> \<sigma>"
  shows "welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau> \<longleftrightarrow> welltyped \<F> \<V> t \<tau>"
proof(rule iffI)
  assume "welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau>"
  thus "welltyped \<F> \<V> t \<tau>"
  proof(induction "t \<cdot>t \<sigma>" \<tau>  arbitrary: t rule: welltyped.induct)
    case (Var x \<tau>)
    then obtain x' where t: "t = Var x'"
      by (metis subst_apply_eq_Var)

    have "welltyped \<F> \<V> t (\<V> x')"
      unfolding t 
      by (simp add: welltyped.Var)

    have "welltyped \<F> \<V> t (\<V> x)"
      using Var welltyped\<^sub>\<sigma>
      unfolding t welltyped\<^sub>\<sigma>_def
      by (metis eval_term.simps(1) welltyped.Var right_uniqueD welltyped_right_unique)

    then have \<V>_x': "\<tau> = \<V> x'"
      using Var welltyped\<^sub>\<sigma>
      unfolding welltyped\<^sub>\<sigma>_def  t
      by (metis welltyped.Var right_uniqueD welltyped_right_unique t)

    show ?case 
      unfolding t \<V>_x'
      by (simp add: welltyped.Var)
  next
    case (Fun f \<tau>s \<tau> ts)
    show ?case 
    proof(cases t)
      case (Var x)
      from Fun show ?thesis
        using welltyped\<^sub>\<sigma>
        unfolding welltyped\<^sub>\<sigma>_def Var
        by (metis (no_types, opaque_lifting) eval_term.simps(1) welltyped.simps prod.sel(2) 
            term.distinct(1) term.inject(2))
    next
      case Fun\<^sub>t: Fun
      with Fun show ?thesis
        by (simp add: welltyped.simps list.rel_map(1) list_all2_mono)
    qed
  qed
next
  assume "welltyped \<F> \<V> t \<tau>"
  thus "welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau>"
  proof(induction t \<tau>  rule: welltyped.induct)
    case Var\<^sub>t: (Var x \<tau>)
    then show ?case
    proof(cases "Var x \<cdot>t \<sigma>")
      case Var
      then show ?thesis
        using welltyped\<^sub>\<sigma>
        unfolding welltyped\<^sub>\<sigma>_def
        by (metis Var\<^sub>t.hyps eval_term.simps(1))        
    next
      case Fun
      then show ?thesis
        using welltyped\<^sub>\<sigma>
        unfolding welltyped\<^sub>\<sigma>_def
        by (metis Var\<^sub>t.hyps eval_term.simps(1))    
    qed
  next
    case (Fun f \<tau>s \<tau> ts)
    then show ?case
      using assms list_all2_mono
      unfolding welltyped\<^sub>\<sigma>_def
      by (smt (verit, ccfv_SIG) eval_term.simps(2) welltyped.simps list.rel_map(1))
  qed
qed

lemma has_type\<^sub>\<sigma>_has_type\<^sub>a: 
  assumes "has_type\<^sub>\<sigma> \<F> \<V> \<sigma>" "has_type\<^sub>a \<F> \<V> a"
  shows "has_type\<^sub>a \<F> \<V> (a \<cdot>a \<sigma>)"
  using assms has_type\<^sub>\<sigma>_has_type
  unfolding has_type\<^sub>a_def subst_atom_def
  by(cases a) fastforce

lemma welltyped\<^sub>\<sigma>_welltyped\<^sub>a: 
  assumes welltyped\<^sub>\<sigma>: "welltyped\<^sub>\<sigma> \<F> \<V> \<sigma>"
  shows "welltyped\<^sub>a \<F> \<V> (a \<cdot>a \<sigma>) \<longleftrightarrow> welltyped\<^sub>a \<F> \<V> a"
  using welltyped\<^sub>\<sigma>_welltyped[OF welltyped\<^sub>\<sigma>]
  unfolding welltyped\<^sub>a_def subst_atom_def
  by(cases a) simp

lemma has_type\<^sub>\<sigma>_has_type\<^sub>l: 
  assumes "has_type\<^sub>\<sigma> \<F> \<V> \<sigma>" "has_type\<^sub>l \<F> \<V> l"
  shows "has_type\<^sub>l \<F> \<V> (l \<cdot>l \<sigma>)"
  using assms has_type\<^sub>\<sigma>_has_type\<^sub>a
  unfolding has_type\<^sub>l_def subst_literal_def
  by(cases l) auto

lemma welltyped\<^sub>\<sigma>_welltyped\<^sub>l: 
  assumes welltyped\<^sub>\<sigma>: "welltyped\<^sub>\<sigma> \<F> \<V> \<sigma>"
  shows "welltyped\<^sub>l \<F> \<V> (l \<cdot>l \<sigma>) \<longleftrightarrow> welltyped\<^sub>l \<F> \<V> l"
  using welltyped\<^sub>\<sigma>_welltyped\<^sub>a[OF welltyped\<^sub>\<sigma>]
  unfolding welltyped\<^sub>l_def subst_literal_def
  by(cases l) auto

lemma has_type\<^sub>\<sigma>_has_type\<^sub>c: 
  assumes "has_type\<^sub>\<sigma> \<F> \<V> \<sigma>" "has_type\<^sub>c \<F> \<V> c"
  shows "has_type\<^sub>c \<F> \<V> (c \<cdot> \<sigma>)"
  using assms has_type\<^sub>\<sigma>_has_type\<^sub>l
  unfolding has_type\<^sub>c_def subst_clause_def
  by blast

lemma welltyped\<^sub>\<sigma>_welltyped\<^sub>c: 
  assumes welltyped\<^sub>\<sigma>: "welltyped\<^sub>\<sigma> \<F> \<V> \<sigma>"
  shows "welltyped\<^sub>c \<F> \<V> (c \<cdot> \<sigma>) \<longleftrightarrow> welltyped\<^sub>c \<F> \<V> c"
  using welltyped\<^sub>\<sigma>_welltyped\<^sub>l[OF welltyped\<^sub>\<sigma>]
  unfolding welltyped\<^sub>c_def subst_clause_def
  by blast

lemma has_type\<^sub>\<kappa>:
  assumes
    \<kappa>_type: "has_type \<F> \<V> \<kappa>\<langle>t\<rangle> \<tau>\<^sub>1" and
    t_type: "has_type \<F> \<V> t \<tau>\<^sub>2" and
    t'_type: "has_type \<F> \<V> t' \<tau>\<^sub>2"
  shows 
    "has_type \<F> \<V> \<kappa>\<langle>t'\<rangle> \<tau>\<^sub>1"
  using \<kappa>_type
proof(induction \<kappa> arbitrary: \<tau>\<^sub>1)
  case Hole
  then show ?case 
    using has_type_right_unique right_uniqueD t'_type t_type by fastforce
next
  case More
  then show ?case 
    by (simp add: has_type.simps)
qed

lemma welltyped\<^sub>\<kappa>:
  assumes
    \<kappa>_type: "welltyped \<F> \<V> \<kappa>\<langle>t\<rangle> \<tau>\<^sub>1" and
    t_type: "welltyped \<F> \<V> t \<tau>\<^sub>2" and
    t'_type: "welltyped \<F> \<V> t' \<tau>\<^sub>2"
  shows 
    "welltyped \<F> \<V> \<kappa>\<langle>t'\<rangle> \<tau>\<^sub>1"
  using \<kappa>_type
proof (induction \<kappa> arbitrary: \<tau>\<^sub>1)
  case Hole
  then show ?case
    using t_type t'_type
    using welltyped_right_unique[of \<F>, THEN right_uniqueD]
    by auto
next
  case (More f ss1 \<kappa> ss2)
  have "welltyped \<F> \<V> (Fun f (ss1 @ \<kappa>\<langle>t\<rangle> # ss2)) \<tau>\<^sub>1"
    using More.prems by simp
  hence "welltyped \<F> \<V> (Fun f (ss1 @ \<kappa>\<langle>t'\<rangle> # ss2)) \<tau>\<^sub>1"
  proof (cases \<F> \<V> "Fun f (ss1 @ \<kappa>\<langle>t\<rangle> # ss2)" \<tau>\<^sub>1 rule: welltyped.cases)
    case (Fun \<tau>s)
    show ?thesis
    proof (rule welltyped.Fun)
      show "\<F> f = (\<tau>s, \<tau>\<^sub>1)"
        using \<open>\<F> f = (\<tau>s, \<tau>\<^sub>1)\<close> .
    next
      show "list_all2 (welltyped \<F> \<V>) (ss1 @ \<kappa>\<langle>t'\<rangle> # ss2) \<tau>s"
        using \<open>list_all2 (welltyped \<F> \<V>) (ss1 @ \<kappa>\<langle>t\<rangle> # ss2) \<tau>s\<close>
        using More.IH
        by (smt (verit, del_insts) list_all2_Cons1 list_all2_append1 list_all2_lengthD)
    qed
  qed
  thus ?case
    by simp
qed

lemma has_type\<^sub>\<sigma>_Var: "has_type\<^sub>\<sigma> \<F> \<V> Var"
  unfolding has_type\<^sub>\<sigma>_def
  by simp

lemma welltyped\<^sub>\<sigma>_Var: "welltyped\<^sub>\<sigma> \<F> \<V> Var"
  unfolding welltyped\<^sub>\<sigma>_def
  by (simp add: welltyped.Var)

lemma welltyped_is_imgu:
  assumes "welltyped \<F> \<V> t \<tau>" "welltyped \<F> \<V> t' \<tau>" "term_subst.is_imgu \<mu> {{t, t'}}"
  shows "welltyped\<^sub>\<sigma> \<F> \<V> \<mu>"
  sorry

(*lemma Fun_arg_types:
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
    "\<forall>\<tau>. has_type \<F> \<V> (Fun f ts) \<tau> \<longrightarrow> has_type \<F> \<V> (Fun f ss) \<tau>" 
    "\<forall>\<tau>. has_type \<F> \<V> (Fun f ss) \<tau> \<longrightarrow> has_type \<F> \<V> (Fun f ts) \<tau>" 
    "zip_option ts ss = Some ds" 
  shows 
    "\<forall>(a, b) \<in> set ds. \<forall>\<tau>. (has_type \<F> \<V> a \<tau> \<longrightarrow> has_type \<F> \<V> b \<tau>) \<and> (has_type \<F> \<V> b \<tau> \<longrightarrow> has_type \<F> \<V> a \<tau>)"
proof-
  have
      "\<forall>\<tau>s. list_all2 (has_type \<F> \<V>) ts \<tau>s \<longrightarrow> list_all2 (has_type \<F> \<V>) ss \<tau>s"
      "\<forall>\<tau>s. list_all2 (has_type \<F> \<V>) ss \<tau>s \<longrightarrow> list_all2 (has_type \<F> \<V>) ts \<tau>s"
      using assms(1,2)
       apply auto
      sorry

  with assms(3) show ?thesis
  proof(induction ts ss arbitrary: ds rule: zip_induct)
    case (Cons_Cons t ts s ss)
    then obtain d' ds' where ds: "ds = d' # ds'"
      by auto

    have
      "\<forall>\<tau>s. list_all2 (has_type \<F> \<V>) (t # ts) \<tau>s \<longrightarrow> (\<exists>\<tau>' \<tau>s'. \<tau>s = \<tau>' # \<tau>s')"
      "\<forall>\<tau>s. list_all2 (has_type \<F> \<V>) (s # ss) \<tau>s \<longrightarrow> (\<exists>\<tau>' \<tau>s'. \<tau>s = \<tau>' # \<tau>s')"
      by (metis list.exhaust list.rel_distinct(2))+

    have "\<forall>\<tau>' \<tau>s'. list_all2 (has_type \<F> \<V>) (t # ts) (\<tau>' # \<tau>s') \<longrightarrow> list_all2 (has_type \<F> \<V>) ts \<tau>s'"
      by simp

    then have 
      "\<forall>\<tau>s. list_all2 (has_type \<F> \<V>) ts \<tau>s \<longrightarrow> list_all2 (has_type \<F> \<V>) ss \<tau>s"
      "\<forall>\<tau>s. list_all2 (has_type \<F> \<V>) ss \<tau>s \<longrightarrow> list_all2 (has_type \<F> \<V>) ts \<tau>s"
      using Cons_Cons(3, 4)
      sorry

    moreover have "zip_option ts ss = Some ds'"
      using Cons_Cons(2) 
      unfolding ds
      by fastforce

  
    ultimately have 
      "\<forall>(t, s)\<in>set ds'. \<forall>\<tau>. (has_type \<F> \<V> t \<tau> \<longrightarrow> has_type \<F> \<V> s \<tau>) \<and> (has_type \<F> \<V> s \<tau> \<longrightarrow> has_type \<F> \<V> t \<tau>)"
      using Cons_Cons.IH
      by presburger

    moreover have "\<forall>\<tau>. (has_type \<F> \<V> t \<tau> \<longrightarrow> has_type \<F> \<V> s \<tau>) \<and> (has_type \<F> \<V> s \<tau> \<longrightarrow> has_type \<F> \<V> t \<tau>)"
      using Cons_Cons.prems
      sorry

    ultimately show ?case
      using Cons_Cons.prems(1) ds
      by auto
  qed(auto)
qed

lemma welltyped_decompose':
  assumes
    "\<forall>\<tau>. has_type \<F> \<V> (Fun f fs) \<tau> \<longrightarrow> has_type \<F> \<V> (Fun f gs) \<tau>" 
    "\<forall>\<tau>. has_type \<F> \<V> (Fun f gs) \<tau> \<longrightarrow> has_type \<F> \<V> (Fun f fs) \<tau>" 
    "decompose (Fun f fs) (Fun f gs) = Some ds"
  shows "\<forall>(t, t') \<in> set ds. \<forall>\<tau>. (has_type \<F> \<V> t \<tau> \<longrightarrow> has_type \<F> \<V> t' \<tau>) \<and> (has_type \<F> \<V> t' \<tau> \<longrightarrow> has_type \<F> \<V> t \<tau>)"
  using welltyped_zip_option assms
  unfolding decompose_def
  by (smt (verit, del_insts) assms(3) case_prodI2 case_prod_conv decompose_Some length_zip zip_option_same zip_option_zip_conv) 

lemma welltyped_decompose:
  assumes
    "\<forall>\<tau> .has_type \<F> \<V> f \<tau> \<longrightarrow> has_type \<F> \<V> g \<tau>" 
    "\<forall>\<tau>. has_type \<F> \<V> g \<tau> \<longrightarrow> has_type \<F> \<V> f \<tau>" 
    "decompose f g = Some ds"
  shows "\<forall>(t, t') \<in> set ds. \<forall>\<tau>. (has_type \<F> \<V> t \<tau> \<longrightarrow> has_type \<F> \<V> t' \<tau>) \<and> (has_type \<F> \<V> t' \<tau> \<longrightarrow> has_type \<F> \<V> t \<tau>)"
proof-
  obtain f' fs gs where "f = Fun f' fs" "g = Fun f' gs"
    using assms(3)
    unfolding decompose_def
    by (smt (z3) option.distinct(1) prod.simps(2) rel_option_None1 term.split_sels(2))

  then show ?thesis
    using assms welltyped_decompose'
    by (smt (verit, ccfv_SIG) case_prodI2 case_prod_conv) 
qed

lemma welltyped_subst'_subst: 
  assumes "\<forall>\<tau>. has_type \<F> \<V> (Var x) \<tau> \<longrightarrow> has_type \<F> \<V> t \<tau>"
  shows "well_typed_subst' \<F> \<V> (subst x t)"
  using assms
  unfolding subst_def well_typed_subst'_def
  by (auto simp add: has_type.Var well_typed_subst_def well_typed_subst_term)

lemma welltyped_unify:
  assumes 
    "unify es bs = Some unifier"
    "\<forall>(t, t') \<in> set es. \<forall>\<tau>. (has_type \<F> \<V> t \<tau> \<longrightarrow> has_type \<F> \<V> t' \<tau>) \<and> (has_type \<F> \<V> t' \<tau> \<longrightarrow> has_type \<F> \<V> t \<tau>)"
    "well_typed_subst' \<F> \<V> (subst_of bs)"
  shows "well_typed_subst' \<F> \<V> (subst_of unifier)"
  using assms
proof(induction es bs arbitrary: unifier rule: unify.induct)
  case (1 bs)
  then show ?case
    by simp
next
  case (2 f ss g ts E bs)
  then have
    "\<forall>\<tau>. (has_type \<F> \<V> (Fun f ss) \<tau> \<longrightarrow> has_type \<F> \<V> (Fun g ts) \<tau>) \<and> (has_type \<F> \<V> (Fun g ts) \<tau> \<longrightarrow> has_type \<F> \<V> (Fun f ss) \<tau>)"
    by auto

  obtain ds where ds: "decompose (Fun f ss) (Fun g ts) = Some ds"
    using 2(2)
    by(simp split: option.splits)

  moreover then have "unify (ds @ E) bs = Some unifier"
    using "2.prems"(1) by auto

  moreover have "\<forall>(t, t') \<in> set ds. \<forall>\<tau>. (has_type \<F> \<V> t \<tau> \<longrightarrow> has_type \<F> \<V> t' \<tau>)  \<and> (has_type \<F> \<V> t' \<tau> \<longrightarrow> has_type \<F> \<V> t \<tau>)"
    using 2 welltyped_decompose
    by (smt (verit, ccfv_threshold) \<open>\<forall>\<tau>. (has_type \<F> \<V> (Fun f ss) \<tau> \<longrightarrow> has_type \<F> \<V> (Fun g ts) \<tau>) \<and> (has_type \<F> \<V> (Fun g ts) \<tau> \<longrightarrow> has_type \<F> \<V> (Fun f ss) \<tau>)\<close> case_prodD case_prodI2 ds)

  moreover then have "\<forall>(t, t') \<in> set (ds @ E). \<forall>\<tau>. (has_type \<F> \<V> t \<tau> \<longrightarrow> has_type \<F> \<V> t' \<tau>)  \<and> (has_type \<F> \<V> t' \<tau> \<longrightarrow> has_type \<F> \<V> t \<tau>)"
    using 2
    by auto

  ultimately show ?case 
    using 2(1, 4)
    by presburger
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
      "\<forall>(s, s') \<in> set (subst_list (subst x t) E). \<forall>\<tau>. (has_type \<F> \<V> s \<tau> \<longrightarrow> has_type \<F> \<V> s' \<tau>) \<and> (has_type \<F> \<V> s' \<tau>  \<longrightarrow> has_type \<F> \<V> s \<tau>)"
      unfolding subst_def subst_list_def
      apply auto
       apply (smt (verit, del_insts) "3.prems"(2) case_prodD fun_upd_other fun_upd_same has_type.Var list.set_intros(1) list.set_intros(2) well_typed_subst_def well_typed_subst_term)
      by (smt (verit, del_insts) "3.prems"(2) case_prodD fun_upd_apply has_type.Var list.set_intros(1) list.set_intros(2) well_typed_subst_def well_typed_subst_term)

    moreover have "\<forall>\<tau>. (has_type \<F> \<V> (Var x) \<tau> \<longrightarrow> has_type \<F> \<V> t \<tau>) \<and> (has_type \<F> \<V> t \<tau> \<longrightarrow> has_type \<F> \<V> (Var x) \<tau>)"
      using 3(4) 
      by auto

    moreover then have "well_typed_subst' \<F> \<V> (subst x t)"
      using welltyped_subst'_subst
      by meson

    moreover then have "well_typed_subst' \<F> \<V> (subst_of ((x, t) # bs))"
      using 3(5)
      unfolding well_typed_subst'_def
      by auto

    ultimately show ?thesis 
      using 3(2, 3) False
      by fastforce
  qed
next
  case (4 t ts x E bs)
  then have "unify (subst_list (subst x (Fun t ts)) E) ((x, (Fun t ts)) # bs) = Some unifier"
    by(auto split: if_splits)

  moreover have 
    "\<forall>(s, s') \<in> set E. \<forall>\<tau>. 
        has_type \<F> \<V> (s \<cdot>t Var(x := (Fun t ts))) \<tau> \<longrightarrow> has_type \<F> \<V> (s' \<cdot>t Var(x := (Fun t ts))) \<tau>"
    using 4(3)
    sorry


  moreover then have 
    "\<forall>(s, s') \<in> set (subst_list (subst x (Fun t ts)) E). \<forall>\<tau>. 
        has_type \<F> \<V> s \<tau> \<longrightarrow> has_type \<F> \<V> s' \<tau>"
    unfolding subst_def subst_list_def
    by fastforce

  moreover have "well_typed_subst' \<F> \<V> (subst x (Fun t ts))"
    using 4(3) welltyped_subst'_subst
    sorry

  moreover then have "well_typed_subst' \<F> \<V> (subst_of ((x, (Fun t ts)) # bs))"
    using 4(4) 
    unfolding well_typed_subst'_def
    by auto

  ultimately show ?case 
    using 4(1, 2)
    sorry
qed

lemma welltyped_unify':
  assumes 
    unify: "unify [(t, t')] [] = Some unifier" and
    \<tau>: "\<forall>\<tau>. (has_type \<F> \<V> t \<tau> \<longrightarrow> has_type \<F> \<V> t' \<tau>) \<and> (has_type \<F> \<V> t' \<tau> \<longrightarrow> has_type \<F> \<V> t \<tau>)"
  shows "well_typed_subst' \<F> \<V> (subst_of unifier)"
  using assms welltyped_unify[OF unify] \<tau> well_typed_subst'_Var
  by fastforce

lemma welltyped_the_mgu: 
  assumes
    the_mgu: "the_mgu t t' = \<mu>" and
    \<tau>: "\<forall>\<tau>. (has_type \<F> \<V> t \<tau> \<longrightarrow> has_type \<F> \<V> t' \<tau>) \<and> (has_type \<F> \<V> t' \<tau> \<longrightarrow> has_type \<F> \<V> t \<tau>)"
  shows 
    "well_typed_subst' \<F> \<V> \<mu>"
  using assms welltyped_unify'[of t t' _ \<F> \<V>]
  unfolding the_mgu_def mgu_def well_typed_subst'_def 
  by (smt (verit) case_prodI2 option.case_eq_if option.collapse option.sel subst_of_simps(1) well_typed_subst'_Var well_typed_subst'_term welltyped_unify)

lemma aux:
  assumes "well_typed_subst' \<F> \<V> \<upsilon>" "term \<cdot>t \<upsilon> = term' \<cdot>t \<upsilon>"
  shows "\<forall>\<tau>. (has_type \<F> \<V> term \<tau> \<longrightarrow> has_type \<F> \<V> term' \<tau>) \<and> (has_type \<F> \<V> term' \<tau> \<longrightarrow> has_type \<F> \<V> term \<tau>)"
  by (metis assms(1) assms(2) eval_term.simps(1) has_type.Var well_typed_subst'_term well_typed_subst_def well_typed_subst_term)

lemma welltyped_imgu_exists:
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes 
    unified: "term \<cdot>t \<upsilon> = term' \<cdot>t \<upsilon>" and \<upsilon>_welltyped: "well_typed_subst' \<F> \<V> \<upsilon>"
  obtains \<mu> :: "('f, 'v) subst"
  where 
    "\<upsilon> = \<mu> \<odot> \<upsilon>" 
    "term_subst.is_imgu \<mu> {{term, term'}}"
    "well_typed_subst' \<F> \<V> \<mu>"
proof-
  obtain \<mu> where \<mu>: "the_mgu term term' = \<mu>"
    using assms ex_mgu_if_subst_apply_term_eq_subst_apply_term by blast

  have "well_typed_subst' \<F> \<V>  (the_mgu term term')"
    using welltyped_the_mgu[OF \<mu>] aux
    by (metis \<mu> \<upsilon>_welltyped unified)

  then show ?thesis
    using that imgu_exists_extendable[OF unified]
    sorry
    (*by (smt (verit, del_insts) basic_substitution_ops.is_imgu_def imgu_exists singletonD subst_compose_assoc term_subst.is_unifier_set_def term_subst.subst_imgu_eq_subst_imgu the_mgu the_mgu_is_unifier unified)
  *)
qed*)

end
