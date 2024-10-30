theory First_Order_Type_System
  imports First_Order_Clause Fun_Extra
begin

type_synonym ('f, 'ty) fun_types = "'f \<Rightarrow> 'ty list \<times> 'ty"
type_synonym ('v, 'ty) var_types = "'v \<Rightarrow> 'ty"

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

definition welltyped\<^sub>a  where
  [clause_simp]: "welltyped\<^sub>a \<F> \<V> A \<longleftrightarrow> (\<exists>\<tau>. \<forall>t \<in> set_uprod A. welltyped \<F> \<V> t \<tau>)"

definition has_type\<^sub>l where
  "has_type\<^sub>l \<F> \<V> L \<longleftrightarrow> has_type\<^sub>a \<F> \<V> (atm_of L)"

definition welltyped\<^sub>l where
   [clause_simp]: "welltyped\<^sub>l \<F> \<V> L \<longleftrightarrow> welltyped\<^sub>a \<F> \<V> (atm_of L)"

definition has_type\<^sub>c where
  "has_type\<^sub>c \<F> \<V> C \<longleftrightarrow> (\<forall>L \<in># C. has_type\<^sub>l \<F> \<V> L)"

definition welltyped\<^sub>c where
  "welltyped\<^sub>c \<F> \<V> C \<longleftrightarrow> (\<forall>L \<in># C. welltyped\<^sub>l \<F> \<V> L)"

definition has_type\<^sub>c\<^sub>s where
  "has_type\<^sub>c\<^sub>s \<F> \<V> N \<longleftrightarrow> (\<forall>C \<in> N. has_type\<^sub>c \<F> \<V> C)"

definition welltyped\<^sub>c\<^sub>s where
  "welltyped\<^sub>c\<^sub>s \<F> \<V> N \<longleftrightarrow> (\<forall>C \<in> N. welltyped\<^sub>c \<F> \<V> C)"

definition has_type\<^sub>\<sigma> where
  "has_type\<^sub>\<sigma> \<F> \<V> \<sigma> \<longleftrightarrow> (\<forall>t \<tau>. has_type \<F> \<V> t \<tau> \<longrightarrow> has_type \<F> \<V> (t \<cdot>t \<sigma>) \<tau>)"

definition has_type\<^sub>\<sigma>' where
  "has_type\<^sub>\<sigma>' \<F> \<V> \<sigma> \<longleftrightarrow> (\<forall>x. has_type \<F> \<V> (\<sigma> x) (\<V> x))"

definition welltyped\<^sub>\<sigma> where
  "welltyped\<^sub>\<sigma> \<F> \<V> \<sigma> \<longleftrightarrow> (\<forall>x. welltyped \<F> \<V> (\<sigma> x) (\<V> x))"

lemma welltyped\<^sub>\<sigma>_Var[simp]: "welltyped\<^sub>\<sigma> \<F> \<V> Var"
  unfolding welltyped\<^sub>\<sigma>_def
  by (simp add: welltyped.intros)

definition welltyped\<^sub>\<sigma>_on where
  "welltyped\<^sub>\<sigma>_on X \<F> \<V> \<sigma> \<longleftrightarrow> (\<forall>x \<in> X. welltyped \<F> \<V> (\<sigma> x) (\<V> x))"

lemma welltyped\<^sub>\<sigma>_welltyped\<^sub>\<sigma>_on:
  "welltyped\<^sub>\<sigma> \<F> \<V> \<sigma> = welltyped\<^sub>\<sigma>_on UNIV \<F> \<V> \<sigma>"
  unfolding welltyped\<^sub>\<sigma>_def welltyped\<^sub>\<sigma>_on_def
  by blast

lemma welltyped\<^sub>\<sigma>_on_subset:
  assumes "welltyped\<^sub>\<sigma>_on Y \<F> \<V> \<sigma>" "X \<subseteq> Y"
  shows "welltyped\<^sub>\<sigma>_on X \<F> \<V> \<sigma>"
  using assms
  unfolding welltyped\<^sub>\<sigma>_on_def
  by blast

definition welltyped\<^sub>\<sigma>' where
  "welltyped\<^sub>\<sigma>' \<F> \<V> \<sigma> \<longleftrightarrow>  (\<forall>t \<tau>. welltyped \<F> \<V> t \<tau> \<longrightarrow> welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau>)"

lemma has_type\<^sub>c_add_mset [clause_simp]: 
  "has_type\<^sub>c \<F> \<V> (add_mset L C) \<longleftrightarrow> has_type\<^sub>l \<F> \<V> L \<and> has_type\<^sub>c \<F> \<V> C"
  by (simp add: has_type\<^sub>c_def)

lemma welltyped\<^sub>c_add_mset [clause_simp]: 
  "welltyped\<^sub>c \<F> \<V> (add_mset L C) \<longleftrightarrow> welltyped\<^sub>l \<F> \<V> L \<and> welltyped\<^sub>c \<F> \<V> C"
  by (simp add: welltyped\<^sub>c_def)

lemma has_type\<^sub>c_plus [clause_simp]: 
  "has_type\<^sub>c \<F> \<V> (C + D) \<longleftrightarrow> has_type\<^sub>c \<F> \<V> C \<and> has_type\<^sub>c \<F> \<V> D"
  by (auto simp: has_type\<^sub>c_def)

lemma welltyped\<^sub>c_plus [clause_simp]: 
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
        by (metis (no_types, opaque_lifting) eval_term.simps(1) prod.sel(2) 
            term.distinct(1) term.inject(2) welltyped.simps)
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
  unfolding has_type\<^sub>a_def atom.subst_def
  by(cases a) fastforce

lemma welltyped\<^sub>\<sigma>_welltyped\<^sub>a: 
  assumes welltyped\<^sub>\<sigma>: "welltyped\<^sub>\<sigma> \<F> \<V> \<sigma>"
  shows "welltyped\<^sub>a \<F> \<V> (a \<cdot>a \<sigma>) \<longleftrightarrow> welltyped\<^sub>a \<F> \<V> a"
  using welltyped\<^sub>\<sigma>_welltyped[OF welltyped\<^sub>\<sigma>]
  unfolding welltyped\<^sub>a_def atom.subst_def
  by(cases a) simp

lemma has_type\<^sub>\<sigma>_has_type\<^sub>l: 
  assumes "has_type\<^sub>\<sigma> \<F> \<V> \<sigma>" "has_type\<^sub>l \<F> \<V> l"
  shows "has_type\<^sub>l \<F> \<V> (l \<cdot>l \<sigma>)"
  using assms has_type\<^sub>\<sigma>_has_type\<^sub>a
  unfolding has_type\<^sub>l_def literal.subst_def
  by(cases l) auto

lemma welltyped\<^sub>\<sigma>_welltyped\<^sub>l: 
  assumes welltyped\<^sub>\<sigma>: "welltyped\<^sub>\<sigma> \<F> \<V> \<sigma>"
  shows "welltyped\<^sub>l \<F> \<V> (l \<cdot>l \<sigma>) \<longleftrightarrow> welltyped\<^sub>l \<F> \<V> l"
  using welltyped\<^sub>\<sigma>_welltyped\<^sub>a[OF welltyped\<^sub>\<sigma>]
  unfolding welltyped\<^sub>l_def literal.subst_def
  by(cases l) auto

lemma has_type\<^sub>\<sigma>_has_type\<^sub>c: 
  assumes "has_type\<^sub>\<sigma> \<F> \<V> \<sigma>" "has_type\<^sub>c \<F> \<V> c"
  shows "has_type\<^sub>c \<F> \<V> (c \<cdot> \<sigma>)"
  using assms has_type\<^sub>\<sigma>_has_type\<^sub>l
  unfolding has_type\<^sub>c_def clause.subst_def
  by blast

lemma welltyped\<^sub>\<sigma>_on_welltyped: 
  assumes wt: "welltyped\<^sub>\<sigma>_on (term.vars t) \<F> \<V> \<sigma>"
  shows "welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau> \<longleftrightarrow> welltyped \<F> \<V> t \<tau>"
proof(rule iffI)
  assume "welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau>"
  thus "welltyped \<F> \<V> t \<tau>"
    using wt
  proof(induction "t \<cdot>t \<sigma>" \<tau>  arbitrary: t rule: welltyped.induct)
    case (Var x \<tau>)
    then obtain x' where t: "t = Var x'"
      by (metis subst_apply_eq_Var)

    have "welltyped \<F> \<V> t (\<V> x')"
      unfolding t 
      by (simp add: welltyped.Var)

    have "welltyped \<F> \<V> t (\<V> x)"
      using Var
      unfolding t welltyped\<^sub>\<sigma>_on_def
      by (auto intro: welltyped.Var elim: welltyped.cases)

    then have \<V>_x': "\<tau> = \<V> x'"
      using Var
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
        using Fun
        unfolding welltyped\<^sub>\<sigma>_def Var
        by (simp add: welltyped.simps welltyped\<^sub>\<sigma>_on_def)
    next
      case Fun\<^sub>t: (Fun f' ts')
      hence "f = f'" and "ts = map (\<lambda>t. t \<cdot>t \<sigma>) ts'"
        using \<open>Fun f ts = t \<cdot>t \<sigma>\<close> by simp_all

      show ?thesis
        unfolding Fun\<^sub>t
      proof (rule welltyped.Fun)
        show "\<F> f' = (\<tau>s, \<tau>)"
          using Fun.hyps \<open>f = f'\<close> by argo
      next
        show "list_all2 (welltyped \<F> \<V>) ts' \<tau>s"
        proof (rule list.rel_mono_strong)
          show "list_all2 (\<lambda>x x2. welltyped \<F> \<V> (x \<cdot>t \<sigma>) x2 \<and>
            (\<forall>xa. x \<cdot>t \<sigma> = xa \<cdot>t \<sigma> \<longrightarrow> welltyped\<^sub>\<sigma>_on (term.vars xa) \<F> \<V> \<sigma> \<longrightarrow> welltyped \<F> \<V> xa x2))
            ts' \<tau>s"
            using Fun.hyps
            unfolding \<open>ts = map (\<lambda>t. t \<cdot>t \<sigma>) ts'\<close> list.rel_map
            by argo
        next
          fix t' \<tau>'
          assume
            "t' \<in> set ts'" and
            "\<tau>' \<in> set \<tau>s" and
            "welltyped \<F> \<V> (t' \<cdot>t \<sigma>) \<tau>' \<and>
              (\<forall>xa. t' \<cdot>t \<sigma> = xa \<cdot>t \<sigma> \<longrightarrow> welltyped\<^sub>\<sigma>_on (term.vars xa) \<F> \<V> \<sigma> \<longrightarrow> 
                  welltyped \<F> \<V> xa \<tau>')"
          thus "welltyped \<F> \<V> t' \<tau>'"
            using Fun.prems Fun.hyps
            by (simp add: Fun\<^sub>t welltyped\<^sub>\<sigma>_on_def)
        qed
      qed
    qed
  qed
next
  assume "welltyped \<F> \<V> t \<tau>"
  thus "welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau>"
    using wt
  proof(induction t \<tau>  rule: welltyped.induct)
    case Var\<^sub>t: (Var x \<tau>)
    thus ?case
      by (cases "Var x \<cdot>t \<sigma>") (simp_all add: welltyped\<^sub>\<sigma>_on_def)
  next
    case (Fun f \<tau>s \<tau> ts)

    show ?case
      unfolding eval_term.simps
    proof (rule welltyped.Fun)
      show "\<F> f = (\<tau>s, \<tau>)"
        using Fun by argo
    next
      show "list_all2 (welltyped \<F> \<V>) (map (\<lambda>s. s \<cdot>t \<sigma>) ts) \<tau>s"
        unfolding list.rel_map
        using Fun.IH
      proof (rule list.rel_mono_strong)
        fix t and \<tau>'
        assume
          "t \<in> set ts" and
          "\<tau>' \<in> set \<tau>s" and
          "welltyped \<F> \<V> t \<tau>' \<and> (welltyped\<^sub>\<sigma>_on (term.vars t) \<F> \<V> \<sigma> \<longrightarrow> welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau>')"
        thus "welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau>'"
          using Fun.prems
          by (simp add: welltyped\<^sub>\<sigma>_on_def)
      qed
    qed
  qed
qed

lemma welltyped\<^sub>\<sigma>_on_welltyped\<^sub>a: 
  assumes wt: "welltyped\<^sub>\<sigma>_on (atom.vars A) \<F> \<V> \<sigma>"
  shows "welltyped\<^sub>a \<F> \<V> (A \<cdot>a \<sigma>) \<longleftrightarrow> welltyped\<^sub>a \<F> \<V> A"
proof (cases A)
  case (Upair t t')

  have "welltyped\<^sub>\<sigma>_on (term.vars t) \<F> \<V> \<sigma>" "welltyped\<^sub>\<sigma>_on (term.vars t') \<F> \<V> \<sigma>"
    using wt unfolding Upair by (simp_all add: welltyped\<^sub>\<sigma>_on_def atom.vars_def)

  hence "(\<exists>\<tau>. welltyped \<F> \<V> (t \<cdot>t \<sigma>) \<tau> \<and> welltyped \<F> \<V> (t' \<cdot>t \<sigma>) \<tau>) =
    (\<exists>\<tau>. welltyped \<F> \<V> t \<tau> \<and> welltyped \<F> \<V> t' \<tau>)"
    using welltyped\<^sub>\<sigma>_on_welltyped by metis

  thus ?thesis
    using Upair
    by (simp add: atom.subst_def welltyped\<^sub>a_def)
qed

lemma welltyped\<^sub>l_iff_welltyped\<^sub>a: "welltyped\<^sub>l \<F> \<V> L \<longleftrightarrow> welltyped\<^sub>a \<F> \<V> (atm_of L)"
  by (cases L) (simp_all add: welltyped\<^sub>l_def)

lemma welltyped\<^sub>\<sigma>_on_welltyped\<^sub>l: 
  assumes wt: "welltyped\<^sub>\<sigma>_on (literal.vars L) \<F> \<V> \<sigma>"
  shows "welltyped\<^sub>l \<F> \<V> (L \<cdot>l \<sigma>) \<longleftrightarrow> welltyped\<^sub>l \<F> \<V> L"
  unfolding welltyped\<^sub>l_iff_welltyped\<^sub>a subst_literal
proof (rule welltyped\<^sub>\<sigma>_on_welltyped\<^sub>a)
  have "atom.vars (atm_of L) = literal.vars L"
    by (cases L) clause_auto
  thus "welltyped\<^sub>\<sigma>_on (atom.vars (atm_of L)) \<F> \<V> \<sigma>"
    using wt
    by simp
qed

lemma welltyped\<^sub>\<sigma>_on_welltyped\<^sub>c: 
  assumes wt: "welltyped\<^sub>\<sigma>_on (clause.vars C) \<F> \<V> \<sigma>"
  shows "welltyped\<^sub>c \<F> \<V> (C \<cdot> \<sigma>) \<longleftrightarrow> welltyped\<^sub>c \<F> \<V> C"
proof -
  have "welltyped\<^sub>l \<F> \<V> (L \<cdot>l \<sigma>) \<longleftrightarrow> welltyped\<^sub>l \<F> \<V> L" if "L \<in># C" for L
  proof (rule welltyped\<^sub>\<sigma>_on_welltyped\<^sub>l)
    have "literal.vars L \<subseteq> clause.vars C"
      using \<open>L \<in># C\<close>
      by (simp add: UN_upper clause.vars_def)
    thus "welltyped\<^sub>\<sigma>_on (literal.vars L) \<F> \<V> \<sigma>"
      using wt welltyped\<^sub>\<sigma>_on_subset by metis
  qed

  thus ?thesis
    unfolding welltyped\<^sub>c_def clause.subst_def
    by simp
qed

lemma welltyped\<^sub>\<sigma>_welltyped\<^sub>c: 
  assumes welltyped\<^sub>\<sigma>: "welltyped\<^sub>\<sigma> \<F> \<V> \<sigma>"
  shows "welltyped\<^sub>c \<F> \<V> (c \<cdot> \<sigma>) \<longleftrightarrow> welltyped\<^sub>c \<F> \<V> c"
  using welltyped\<^sub>\<sigma>_welltyped\<^sub>l[OF welltyped\<^sub>\<sigma>]
  unfolding welltyped\<^sub>c_def clause.subst_def
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

lemma welltyped_subterm:
  assumes "welltyped \<F> \<V> (Fun f ts) \<tau>"
  shows "\<forall>t\<in>set ts. \<exists>\<tau>'. welltyped \<F> \<V> t \<tau>'"
  using assms
proof(induction ts)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ts)
  then show ?case
    by (metis (no_types, lifting) Term.term.simps(4) in_set_conv_nth list_all2_conv_all_nth 
        term.sel(4) welltyped.simps)
qed

lemma welltyped\<^sub>\<kappa>': 
  assumes "welltyped \<F> \<V> \<kappa>\<langle>t\<rangle> \<tau>" 
  shows "\<exists>\<tau>'. welltyped \<F> \<V> t \<tau>'"
  using assms
proof(induction \<kappa> arbitrary: \<tau>)
  case Hole
  then show ?case
    by auto
next
  case (More x1 x2 \<kappa> x4)
  then show ?case 
    by (metis ctxt_apply_term.simps(2) in_set_conv_decomp welltyped_subterm)
    (* AFP Devel:
      by (metis in_set_conv_decomp intp_actxt.simps(2) welltyped_subterm)
    *)
qed


lemma welltyped\<^sub>\<kappa> [clause_intro]:
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
    using t_type t'_type welltyped_right_unique[of \<F>, THEN right_uniqueD]
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

lemma welltyped_add_literal:
  assumes "welltyped\<^sub>c \<F> \<V> P'" "welltyped \<F> \<V> s\<^sub>1 \<tau>" "welltyped \<F> \<V> s\<^sub>2 \<tau>" 
  shows "welltyped\<^sub>c \<F> \<V> (add_mset (s\<^sub>1 !\<approx> s\<^sub>2) P')"
  using assms
  unfolding welltyped\<^sub>c_add_mset welltyped\<^sub>l_def welltyped\<^sub>a_def
  by auto

lemma welltyped_\<V>:
  assumes 
    "\<forall>x\<in>term.vars t. \<V> x = \<V>' x"
    "welltyped \<F> \<V> t \<tau>"
  shows  
    "welltyped \<F> \<V>' t \<tau>"
  using assms(2, 1)
  by(induction rule: welltyped.induct)(auto simp: welltyped.simps list.rel_mono_strong)

lemma welltyped_subst_\<V>:
  assumes 
    "\<forall>x\<in> X. \<V> x = \<V>' x"
    "\<forall>x\<in> X. term.is_ground (\<gamma> x)"
  shows  
    "welltyped\<^sub>\<sigma>_on X \<F> \<V> \<gamma> \<longleftrightarrow> welltyped\<^sub>\<sigma>_on X \<F> \<V>' \<gamma>"
  unfolding welltyped\<^sub>\<sigma>_on_def
  using welltyped_\<V> assms
  by (metis empty_iff)

lemma welltyped\<^sub>a_\<V>:
  assumes 
    "\<forall>x\<in>atom.vars a. \<V> x = \<V>' x"
    "welltyped\<^sub>a \<F> \<V> a"
  shows  
    "welltyped\<^sub>a \<F> \<V>' a"
  using assms
  unfolding welltyped\<^sub>a_def atom.vars_def
  by (metis (full_types) UN_I welltyped_\<V>)

lemma welltyped\<^sub>l_\<V>:
  assumes 
    "\<forall>x\<in> literal.vars l. \<V> x = \<V>' x"
    "welltyped\<^sub>l \<F> \<V> l"
  shows  
    "welltyped\<^sub>l \<F> \<V>' l"
  using assms welltyped\<^sub>a_\<V>
  unfolding welltyped\<^sub>l_def literal.vars_def set_literal_atm_of
  by fastforce

lemma welltyped\<^sub>c_\<V>:
  assumes 
    "\<forall>x\<in> clause.vars c. \<V> x = \<V>' x"
    "welltyped\<^sub>c \<F> \<V> c"
  shows  
    "welltyped\<^sub>c \<F> \<V>' c"
  using assms welltyped\<^sub>l_\<V>
  unfolding welltyped\<^sub>c_def clause.vars_def
  by fastforce

lemma welltyped_renaming':
  assumes 
    "term_subst.is_renaming \<rho>"
    "welltyped\<^sub>\<sigma> typeof_fun \<V> \<rho>"
    "welltyped typeof_fun (\<lambda>x. \<V> (the_inv Var (\<rho> x))) t \<tau>"
  shows "welltyped typeof_fun \<V> (t \<cdot>t \<rho>) \<tau>"
  using assms(3)
proof(induction rule: welltyped.induct)
  case (Var x \<tau>)
  then show ?case 
    using assms(1, 2)
    unfolding welltyped\<^sub>\<sigma>_def
    by (metis comp_apply eval_term.simps(1) inj_on_Var 
        term_subst_is_renaming_iff_ex_inj_fun_on_vars the_inv_f_f welltyped.Var)
next
  case (Fun f \<tau>s \<tau> ts)
  then show ?case
    by (smt (verit, ccfv_SIG) assms(2) list_all2_mono welltyped.Fun welltyped\<^sub>\<sigma>_welltyped)
qed

lemma welltyped\<^sub>a_renaming':
  assumes 
    "term_subst.is_renaming \<rho>"
    "welltyped\<^sub>\<sigma> typeof_fun \<V> \<rho>"
    "welltyped\<^sub>a typeof_fun (\<lambda>x. \<V> (the_inv Var (\<rho> x))) a"
  shows "welltyped\<^sub>a typeof_fun \<V> (a \<cdot>a \<rho>)"
  using welltyped_renaming'[OF assms(1,2)] assms(3)
  unfolding welltyped\<^sub>a_def
  by(cases a)(auto simp: subst_atom)

lemma welltyped\<^sub>l_renaming':
  assumes 
    "term_subst.is_renaming \<rho>"
    "welltyped\<^sub>\<sigma> typeof_fun \<V> \<rho>"
    "welltyped\<^sub>l typeof_fun (\<lambda>x. \<V> (the_inv Var (\<rho> x))) l"
  shows "welltyped\<^sub>l typeof_fun \<V> (l \<cdot>l \<rho>)"
  using welltyped\<^sub>a_renaming'[OF assms(1,2)] assms(3)
  unfolding welltyped\<^sub>l_def subst_literal(3)
  by presburger

lemma welltyped\<^sub>c_renaming':
  assumes 
    "term_subst.is_renaming \<rho>"
    "welltyped\<^sub>\<sigma> typeof_fun \<V> \<rho>"
    "welltyped\<^sub>c typeof_fun (\<lambda>x. \<V> (the_inv Var (\<rho> x))) c"
  shows "welltyped\<^sub>c typeof_fun \<V> (c \<cdot> \<rho>)"
  using welltyped\<^sub>l_renaming'[OF assms(1,2)] assms(3)
  unfolding welltyped\<^sub>c_def
  by (simp add: clause.subst_def)

definition range_vars' :: "('f, 'v) subst \<Rightarrow> 'v set" where                                 
  "range_vars' \<sigma> = \<Union>(term.vars ` range \<sigma>)"

lemma vars_term_range_vars':
  assumes "x \<in> term.vars (t \<cdot>t \<sigma>)"
  shows "x \<in> range_vars' \<sigma>"
  using assms
  unfolding range_vars'_def
  by(induction t) auto

context  
  fixes \<rho> \<V> \<V>'
  assumes 
    renaming: "term_subst.is_renaming \<rho>" and
    range_vars: "\<forall>x \<in> range_vars' \<rho>. \<V> (the_inv \<rho> (Var x)) = \<V>' x"
begin

lemma welltyped_renaming: "welltyped \<F> \<V> t \<tau> \<longleftrightarrow> welltyped \<F> \<V>' (t \<cdot>t \<rho>) \<tau>"
proof(intro iffI)
  assume "welltyped \<F> \<V> t \<tau>"
  then show "welltyped \<F> \<V>' (t \<cdot>t \<rho>) \<tau>"
  proof(induction rule: welltyped.induct)
    case (Var x \<tau>)

    obtain y where y: "Var x \<cdot>t \<rho> = Var y"
      using renaming
      by (metis eval_term.simps(1) term.collapse(1) term_subst_is_renaming_iff)

    then have "y \<in> range_vars' \<rho>"
      using vars_term_range_vars'
      by (metis term.set_intros(3))

    then have "\<V> (the_inv \<rho> (Var y)) = \<V>' y"
      by (simp add: range_vars)

    moreover have "(the_inv \<rho> (Var y)) = x"
      using y renaming
      unfolding term_subst_is_renaming_iff
      by (metis eval_term.simps(1) the_inv_f_f)

    ultimately have "\<V>' y = \<tau>"
      using Var
      by argo

    then show ?case
      unfolding y
      by(rule welltyped.Var)
  next
    case (Fun f \<tau>s \<tau> ts)
    then show ?case
      by (smt (verit, ccfv_SIG) eval_term.simps(2) length_map list_all2_conv_all_nth 
          nth_map welltyped.simps)
  qed
next
  assume "welltyped \<F> \<V>' (t \<cdot>t \<rho>) \<tau>"
  then show " welltyped \<F> \<V> t \<tau>"
  proof(induction t arbitrary: \<tau>)
    case (Var x)
    then obtain y where y: "Var x \<cdot>t \<rho> = Var y"
      using renaming
      by (metis eval_term.simps(1) term.collapse(1) term_subst_is_renaming_iff)

    then have "y \<in> range_vars' \<rho>"
      using vars_term_range_vars'
      by (metis term.set_intros(3))

    then have "\<V> (the_inv \<rho> (Var y)) = \<V>' y"
      by (simp add: range_vars)

    moreover have "(the_inv \<rho> (Var y)) = x"
      using y renaming
      unfolding term_subst_is_renaming_iff
      by (metis eval_term.simps(1) the_inv_f_f)

    moreover have "\<V>' y = \<tau>"
      using Var
      unfolding y
      by (meson right_uniqueD welltyped.Var welltyped_right_unique)

    ultimately have "\<V> x = \<tau>"
      by blast

    then show ?case
      by(rule welltyped.Var)
  next
    case (Fun f ts)
    then show ?case
      by (smt (verit, ccfv_SIG) eval_term.simps(2) list.rel_map(1) list.rel_mono_strong 
          term.distinct(1) term.inject(2) welltyped.simps)
  qed
qed

lemma has_type_renaming: "has_type \<F> \<V> t \<tau> \<longleftrightarrow> has_type \<F> \<V>' (t \<cdot>t \<rho>) \<tau>"
  using renaming range_vars
proof(cases t)
  case (Var x1)
  then show ?thesis
    by (smt (verit, ccfv_SIG) comp_apply eval_term.simps(1) has_type.simps range_vars renaming 
        term.distinct(1) term.set_intros(3) term_subst_is_renaming_iff 
        term_subst_is_renaming_iff_ex_inj_fun_on_vars the_inv_f_f vars_term_range_vars')
next
  case (Fun x21 x22)
  then show ?thesis 
    by (simp add: has_type.simps)
qed

lemma welltyped\<^sub>\<sigma>_renaming_ground_subst: 
  assumes "welltyped\<^sub>\<sigma> \<F> \<V>' \<gamma>" "welltyped\<^sub>\<sigma> \<F> \<V> \<rho>" "term_subst.is_ground_subst \<gamma>"
  shows "welltyped\<^sub>\<sigma> \<F> \<V> (\<rho> \<odot> \<gamma>)"
proof-
  have "\<forall>x \<in> range_vars' \<rho>. welltyped \<F> \<V>' (\<gamma> x) (\<V>' x)"
    using assms 
    unfolding welltyped\<^sub>\<sigma>_def
    by simp

  then have "\<forall>x \<in> range_vars' \<rho>. welltyped \<F> \<V>' (\<gamma> x) (\<V> (the_inv \<rho> (Var x)))"
    using range_vars
    by auto

  then have "\<forall>x \<in> range_vars' \<rho>. welltyped \<F> \<V>' ((\<rho> \<odot> \<gamma>) x) (\<V> x)"
    by (metis assms(1) eval_term.simps(1) subst_compose_def welltyped.Var welltyped\<^sub>\<sigma>_welltyped
        welltyped_renaming)

  then have "\<forall>x \<in> range_vars' \<rho>. welltyped \<F> \<V>' (Var x \<cdot>t (\<rho> \<odot> \<gamma>)) (\<V> x)"
    by auto

  then have "\<forall>x. welltyped \<F> \<V>' (Var x \<cdot>t (\<rho> \<odot> \<gamma>)) (\<V> x)"
    by (metis assms(1) eval_term.simps(1) subst_compose_def welltyped\<^sub>\<sigma>_Var welltyped\<^sub>\<sigma>_def 
        welltyped\<^sub>\<sigma>_welltyped welltyped_renaming)

  then have "\<forall>x \<in> range_vars' \<rho>. welltyped \<F> \<V>' (Var x \<cdot>t \<rho>) (\<V> x)"
    using welltyped\<^sub>\<sigma>_welltyped[OF assms(1)]
    by (simp add: subst_compose_def)

  have "\<forall>x. welltyped \<F> \<V>' (Var x \<cdot>t \<rho>) (\<V> x)"
    by (meson welltyped.Var welltyped_renaming)

  then have "\<forall>x. welltyped \<F> \<V> (Var x \<cdot>t \<rho>) (\<V> x)"
    using welltyped_renaming
    by (meson assms(2) welltyped\<^sub>\<sigma>_welltyped)

  then show "welltyped\<^sub>\<sigma> \<F> \<V> (\<rho> \<odot> \<gamma>)"
    unfolding welltyped\<^sub>\<sigma>_def
    by (metis (mono_tags, lifting) \<open>\<forall>x. welltyped \<F> \<V>' (Var x \<cdot>t \<rho> \<odot> \<gamma>) (\<V> x)\<close> assms(3)
        eval_term.simps(1) term_subst.is_ground_subst_comp_right 
        term_subst.is_ground_subst_is_ground term_subst.subst_ident_if_ground welltyped_renaming)
qed

lemma welltyped\<^sub>a_renaming: "welltyped\<^sub>a \<F> \<V> a \<longleftrightarrow> welltyped\<^sub>a \<F> \<V>' (a \<cdot>a \<rho>)"
  using welltyped_renaming
  unfolding welltyped\<^sub>a_def
  by(cases a)(simp add: subst_atom)

lemma welltyped\<^sub>l_renaming: "welltyped\<^sub>l \<F> \<V> l \<longleftrightarrow> welltyped\<^sub>l \<F> \<V>' (l \<cdot>l \<rho>)"
  using welltyped\<^sub>a_renaming
  unfolding welltyped\<^sub>l_def
  by (simp add: subst_literal(3))

lemma welltyped\<^sub>c_renaming: "welltyped\<^sub>c \<F> \<V> c \<longleftrightarrow> welltyped\<^sub>c \<F> \<V>' (c \<cdot> \<rho>)"
  using welltyped\<^sub>l_renaming
  unfolding welltyped\<^sub>c_def
  by (simp add: clause.subst_def)

end

context  
  fixes \<rho>
  assumes renaming: "term_subst.is_renaming \<rho>"
begin


lemma welltyped_renaming_weaker: 
  assumes "\<forall>x \<in> term.vars (t \<cdot>t \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x"
  shows "welltyped \<F> \<V> t \<tau> \<longleftrightarrow> welltyped \<F> \<V>' (t \<cdot>t \<rho>) \<tau>"
proof(intro iffI)
  assume "welltyped \<F> \<V> t \<tau>"
  then show "welltyped \<F> \<V>' (t \<cdot>t \<rho>) \<tau>"
    using assms
  proof(induction rule: welltyped.induct)
    case (Var x \<tau>)

    obtain y where y: "Var x \<cdot>t \<rho> = Var y"
      using renaming
      by (metis eval_term.simps(1) term.collapse(1) term_subst_is_renaming_iff)

    then have "\<V> (the_inv \<rho> (Var y)) = \<V>' y"
      using Var(2)
      by simp     

    moreover have "(the_inv \<rho> (Var y)) = x"
      using y renaming
      unfolding term_subst_is_renaming_iff
      by (metis eval_term.simps(1) the_inv_f_f)

    ultimately have "\<V>' y = \<tau>"
      using Var
      by argo

    then show ?case
      unfolding y
      by(rule welltyped.Var)
  next
    case (Fun f \<tau>s \<tau> ts)

    have "list_all2 (welltyped \<F> \<V>') (map (\<lambda>s. s \<cdot>t \<rho>) ts) \<tau>s"
      using Fun(2, 3)
      by(auto simp: list.rel_mono_strong list_all2_map1)

    then show ?case
      by (simp add: Fun.hyps welltyped.simps)
  qed
next
  assume "welltyped \<F> \<V>' (t \<cdot>t \<rho>) \<tau>"
  then show " welltyped \<F> \<V> t \<tau>"
    using assms
  proof(induction t arbitrary: \<tau>)
    case (Var x)
    then obtain y where y: "Var x \<cdot>t \<rho> = Var y"
      using renaming
      by (metis eval_term.simps(1) term.collapse(1) term_subst_is_renaming_iff)

    then have "\<V> (the_inv \<rho> (Var y)) = \<V>' y"
      by (simp add: Var)

    moreover have "(the_inv \<rho> (Var y)) = x"
      using y renaming
      unfolding term_subst_is_renaming_iff
      by (metis eval_term.simps(1) the_inv_f_f)

    moreover have "\<V>' y = \<tau>"
      using Var
      unfolding y
      by (meson right_uniqueD welltyped.Var welltyped_right_unique)

    ultimately have "\<V> x = \<tau>"
      by blast

    then show ?case
      by(rule welltyped.Var)
  next
    case (Fun f ts)
    have "\<lbrakk>\<And>x2a \<tau>. \<lbrakk>x2a \<in> set ts; welltyped \<F> \<V>' (x2a \<cdot>t \<rho>) \<tau>\<rbrakk> \<Longrightarrow> welltyped \<F> \<V> x2a \<tau>;
     welltyped \<F> \<V>' (Fun f (map (\<lambda>s. s \<cdot>t \<rho>) ts)) \<tau>;
     \<forall>y\<in>set ts. \<forall>x\<in>term.vars (y \<cdot>t \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x\<rbrakk>
    \<Longrightarrow> welltyped \<F> \<V> (Fun f ts) \<tau>"
      by (smt (verit, best) Term.term.simps(2) Term.term.simps(4) list.rel_mono_strong 
          list_all2_map1 welltyped.simps)

    with Fun show ?case
      by auto
     
  qed
qed

lemma welltyped\<^sub>a_renaming_weaker: 
  assumes"\<forall>x \<in> atom.vars (a \<cdot>a \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x"
  shows "welltyped\<^sub>a \<F> \<V> a \<longleftrightarrow> welltyped\<^sub>a \<F> \<V>' (a \<cdot>a \<rho>)"
proof(cases a)
  case (Upair a b)

  then have 
    "\<And>\<tau>. \<lbrakk>\<And>t \<V> \<V>' \<F> \<tau>.
             \<forall>x\<in>term.vars (t \<cdot>t \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x \<Longrightarrow>
             welltyped \<F> \<V> t \<tau> = welltyped \<F> \<V>' (t \<cdot>t \<rho>) \<tau>;
          \<forall>x\<in>term.vars (a \<cdot>t \<rho>) \<union> term.vars (b \<cdot>t \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x; welltyped \<F> \<V> a \<tau>;
          welltyped \<F> \<V> b \<tau>\<rbrakk>
         \<Longrightarrow> \<exists>\<tau>. welltyped \<F> \<V>' (a \<cdot>t \<rho>) \<tau> \<and> welltyped \<F> \<V>' (b \<cdot>t \<rho>) \<tau>"
     "\<And>\<tau>. \<lbrakk> \<And>t \<V> \<V>' \<F> \<tau>.
             \<forall>x\<in>term.vars (t \<cdot>t \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x \<Longrightarrow>
             welltyped \<F> \<V> t \<tau> = welltyped \<F> \<V>' (t \<cdot>t \<rho>) \<tau>;
          \<forall>x\<in>term.vars (a \<cdot>t \<rho>) \<union> term.vars (b \<cdot>t \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x;
          welltyped \<F> \<V>' (a \<cdot>t \<rho>) \<tau>; welltyped \<F> \<V>' (b \<cdot>t \<rho>) \<tau>\<rbrakk>
         \<Longrightarrow> \<exists>\<tau>. welltyped \<F> \<V> a \<tau> \<and> welltyped \<F> \<V> b \<tau>"
    by (metis UnCI welltyped_renaming_weaker)+

  with Upair show ?thesis
    using welltyped_renaming_weaker  assms
    unfolding welltyped\<^sub>a_def atom.vars_def
    by(auto simp add: subst_atom)
qed

lemma welltyped\<^sub>l_renaming_weaker: 
  assumes "\<forall>x \<in> literal.vars (l \<cdot>l \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x"
  shows "welltyped\<^sub>l \<F> \<V> l \<longleftrightarrow> welltyped\<^sub>l \<F> \<V>' (l \<cdot>l \<rho>)"
  using welltyped\<^sub>a_renaming_weaker assms
  unfolding welltyped\<^sub>l_def literal.vars_def set_literal_atm_of
  by (simp add: subst_literal(3))

lemma welltyped\<^sub>c_renaming_weaker: 
  assumes "\<forall>x \<in> clause.vars (c \<cdot> \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x"
  shows "welltyped\<^sub>c \<F> \<V> c \<longleftrightarrow> welltyped\<^sub>c \<F> \<V>' (c \<cdot> \<rho>)"
  using welltyped\<^sub>l_renaming_weaker assms
  unfolding welltyped\<^sub>c_def  clause.vars_def  clause.subst_def
  by blast

lemma has_type_renaming_weaker:
  assumes "\<forall>x \<in> term.vars (t \<cdot>t \<rho>). \<V> (the_inv \<rho> (Var x)) = \<V>' x"
  shows "has_type \<F> \<V> t \<tau> \<longleftrightarrow> has_type \<F> \<V>' (t \<cdot>t \<rho>) \<tau>"
  using renaming assms
proof(cases t)
  case (Var x1)
  then show ?thesis
    by (smt (verit, ccfv_SIG) Term.term.simps(4) assms eval_term.simps(1) has_type.simps is_Var_def 
        renaming term.set_intros(3) term_subst_is_renaming_iff the_inv_f_f)
next
  case (Fun x21 x22)
  then show ?thesis
    by (simp add: has_type.simps)
qed

lemma welltyped\<^sub>\<sigma>_renaming_ground_subst_weaker: 
  assumes 
    "welltyped\<^sub>\<sigma> \<F> \<V>' \<gamma>" 
    "welltyped\<^sub>\<sigma>_on X \<F> \<V> \<rho>" 
    "term_subst.is_ground_subst \<gamma>" 
    "\<forall>x \<in> \<Union>(term.vars ` \<rho> ` X). \<V> (the_inv \<rho> (Var x)) = \<V>' x"
  shows "welltyped\<^sub>\<sigma>_on X \<F> \<V> (\<rho> \<odot> \<gamma>)"
proof(unfold welltyped\<^sub>\<sigma>_on_def, intro ballI)
  fix x
  assume "x \<in> X"

  then have "welltyped \<F> \<V> (\<rho> x) (\<V> x)"
    using assms(2)
    unfolding welltyped\<^sub>\<sigma>_on_def
    by simp

  obtain y where y: "\<rho> x =  Var y"
    by (metis renaming term.collapse(1) term_subst_is_renaming_iff)

  then have "y \<in> \<Union>(term.vars ` \<rho> ` X)"
    using \<open>x \<in> X\<close> 
    by (metis Union_iff image_eqI term.set_intros(3))

  moreover have "welltyped \<F> \<V> (\<gamma> y) (\<V>' y)"
    using assms(1)
    by (metis assms(3) emptyE eval_term.simps(1) term_subst.is_ground_subst_def welltyped\<^sub>\<sigma>_def 
        welltyped_\<V>)

  ultimately have "welltyped \<F> \<V> (\<gamma> y) (\<V> (the_inv \<rho> (Var y)))"
    using assms(4)
    by metis

  moreover have "the_inv \<rho> (Var y) = x"
    using y renaming
    by (metis term_subst_is_renaming_iff the_inv_f_f)

  moreover have "\<gamma> y = (\<rho> \<odot> \<gamma>) x"
    using y
    by (simp add: subst_compose_def)

  ultimately show "welltyped \<F> \<V> ((\<rho> \<odot> \<gamma>) x) (\<V> x)"
    by argo
qed


end




lemma 
  infinite_even_nat: "infinite { n :: nat . even n }" and 
  infinite_odd_nat: "infinite { n :: nat . odd n }"
  by (metis Suc_leD dual_order.refl even_Suc infinite_nat_iff_unbounded_le mem_Collect_eq)+

lemma obtain_infinite_partition: 
  obtains X Y :: "'a :: {countable, infinite} set" 
  where
    "X \<inter> Y = {}" "X \<union> Y = UNIV" and
    "infinite X" and
    "infinite Y"
proof-
  obtain g :: "'a \<Rightarrow> nat" where "bij g"
    using countableE_infinite[of "UNIV :: 'a set"] infinite_UNIV by blast

  define g' where "g' \<equiv> inv g"

  then have bij_g': "bij g'"
    by (simp add: \<open>bij g\<close> bij_betw_inv_into)

  define X :: "'a set" where 
    "X \<equiv> g' ` { n. even n }"

  define Y :: "'a set" where 
    "Y \<equiv> g' ` { n. odd n }"

  have "X \<inter> Y = {}"
    using bij_g'
    unfolding X_def Y_def
    by (simp add: bij_image_Collect_eq disjoint_iff)

  moreover have "X \<union> Y = UNIV"
    using bij_g'
    unfolding X_def Y_def
    by(auto simp: bij_image_Collect_eq)

  moreover have "bij_betw g' { n. even n } X" "bij_betw g' { n. odd n } Y"
    unfolding X_def Y_def
    by (metis \<open>bij g\<close> bij_betw_imp_surj_on g'_def inj_on_imp_bij_betw inj_on_inv_into top.extremum)+

  then have "infinite X" "infinite Y"
    using infinite_even_nat infinite_odd_nat bij_betw_finite
    by blast+

  ultimately show ?thesis
    using that
    by blast
qed

lemma "(\<Union>n'.{ n. g n = n' }) = UNIV"
  by blast

lemma inv_enumerate:
  assumes "infinite N" 
  shows "(\<lambda>x. inv (enumerate N) x) ` N = UNIV"
  by (metis assms enumerate_in_set inj_enumerate inv_f_eq surj_on_alternative)

instance nat :: infinite
  by(standard) simp

lemma finite_bij_enumerate_inv_into:
  fixes S :: "'a::wellorder set"
  assumes S: "finite S"
  shows "bij_betw (inv_into {..<card S} (enumerate S)) S {..<card S}"
  using finite_bij_enumerate[OF assms] bij_betw_inv_into
  by blast

lemma obtain_inj_test'_on:
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "nat \<Rightarrow> 'ty"
  assumes 
    "finite X" 
    "finite Y" 
    "\<And>ty. infinite {x. \<V>\<^sub>1 x = ty}" 
    "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty}"
  obtains f f' :: "nat \<Rightarrow> nat" where
    "inj f" "inj f'"
    "f ` X \<inter> f' ` Y = {}"
    "\<forall>x \<in> X. \<V>\<^sub>1 (f x) = \<V>\<^sub>1 x"
    "\<forall>x \<in> Y. \<V>\<^sub>2 (f' x) = \<V>\<^sub>2 x"
proof
  have "\<And>ty. infinite ({x. \<V>\<^sub>2 x = ty} - X)"
    by (simp add: assms(1) assms(4))

  then have infinite: "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}"
    by (simp add: set_diff_eq)

  define f' where
    "\<And>x. f' x \<equiv> enumerate {y. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> y \<notin> X} x"


  have f'_not_in_x: "\<And>x. f' x \<notin> X"
  proof-
    fix x
    show "f' x \<notin> X"
      unfolding f'_def
      using enumerate_in_set[OF infinite]
      by (smt (verit) CollectD Collect_cong)
  qed 
 
   show "inj id"
     by simp

   show "inj f'"
   proof(unfold inj_def; intro allI impI)
     fix x y
     assume "f' x = f' y"

     moreover then have "\<V>\<^sub>2 y = \<V>\<^sub>2 x"
       unfolding f'_def
       by (smt (verit, ccfv_SIG) Collect_mono_iff enumerate_in_set infinite mem_Collect_eq 
           rev_finite_subset)

     ultimately show "x = y"
       unfolding f'_def
       by (smt (verit) Collect_cong infinite inj_enumerate inj_onD iso_tuple_UNIV_I)
   qed

   show "id ` X \<inter> f' ` Y = {}"
     using f'_not_in_x
     by auto

   show "\<forall>x\<in>X. \<V>\<^sub>1 (id x) = \<V>\<^sub>1 x"
     by simp

   show "\<forall>x\<in>Y. \<V>\<^sub>2 (f' x) = \<V>\<^sub>2 x" 
     unfolding f'_def
     using enumerate_in_set[OF infinite]
     by (smt (verit) Collect_cong mem_Collect_eq)
 qed

lemma obtain_inj''_on':
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'a :: infinite \<Rightarrow> 'ty"
  assumes "finite X" "finite Y" "\<And>ty. infinite {x. \<V>\<^sub>1 x = ty}" "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty}"
  obtains f f' :: "'a \<Rightarrow> 'a" where
    "inj f" "inj f'"
    "f ` X \<inter> f' ` Y = {}"
    "\<forall>x \<in> X. \<V>\<^sub>1 (f x) = \<V>\<^sub>1 x"
    "\<forall>x \<in> Y. \<V>\<^sub>2 (f' x) = \<V>\<^sub>2 x"
proof
  have "\<And>ty. infinite ({x. \<V>\<^sub>2 x = ty} - X)"
    by (simp add: assms(1) assms(4))

  then have infinite: "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}"
    by (simp add: set_diff_eq)

  have "\<And>ty. |{x. \<V>\<^sub>2 x = ty}| =o |{x. \<V>\<^sub>2 x = ty } - X|"
    using assms(1, 4)
    using card_of_infinite_diff_finite ordIso_symmetric by blast

  then have "\<And>ty. |{x. \<V>\<^sub>2 x = ty}| =o |{x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}|"
    using set_diff_eq[of _ X]
    by auto

  then have exists_g': "\<And>ty. \<exists>g'. bij_betw g' {x. \<V>\<^sub>2 x = ty} {x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}"
    using card_of_ordIso by blast

  define get_g' where
    "\<And>ty. get_g' ty \<equiv> SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = ty} {x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}"

  define f' where
    "\<And>x. f' x \<equiv> get_g' (\<V>\<^sub>2 x) x"

  have f'_not_in_x: "\<And>x. f' x \<notin> X"
  proof-
    fix y

    define g' where "g' \<equiv> SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}"

    have "y \<in> {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y}"
      by simp

    moreover have "g' y \<in> {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}"
    proof-
      have "\<And>g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X} \<Longrightarrow>
          \<V>\<^sub>2 ((SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}) y) = \<V>\<^sub>2 y"
        "\<And>g'. \<lbrakk>bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X};
           (SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}) y \<in> X\<rbrakk>
          \<Longrightarrow> False"
        by (smt (verit, ccfv_SIG) bij_betw_apply mem_Collect_eq verit_sko_ex_indirect)+
        
       then show ?thesis
        unfolding g'_def
        using exists_g'[of "\<V>\<^sub>2 y"]
        by auto
    qed

    then have "g' y \<notin> X"
      by simp

    then show "f' y \<notin> X"
      unfolding f'_def get_g'_def g'_def.
  qed

   show "inj id"
     by simp

   show "inj f'"
   proof(unfold inj_def; intro allI impI)
     fix x y
     assume "f' x = f' y"

     moreover then have "\<V>\<^sub>2 y = \<V>\<^sub>2 x"
       unfolding f'_def get_g'_def
       using someI_ex[OF exists_g']
       by (smt (verit, best) f'_def get_g'_def bij_betw_iff_bijections calculation mem_Collect_eq)

     moreover have "\<And>g'. \<lbrakk>(SOME g'. bij_betw g' {xa. \<V>\<^sub>2 xa = \<V>\<^sub>2 x} {xa. \<V>\<^sub>2 xa = \<V>\<^sub>2 x \<and> xa \<notin> X}) x =
           (SOME g'. bij_betw g' {xa. \<V>\<^sub>2 xa = \<V>\<^sub>2 x} {xa. \<V>\<^sub>2 xa = \<V>\<^sub>2 x \<and> xa \<notin> X}) y;
           \<V>\<^sub>2 y = \<V>\<^sub>2 x; \<And>P x. P x \<Longrightarrow> P (Eps P); 
           bij_betw g' {xa. \<V>\<^sub>2 xa = \<V>\<^sub>2 x} {xa. \<V>\<^sub>2 xa = \<V>\<^sub>2 x \<and> xa \<notin> X}\<rbrakk>
          \<Longrightarrow> x = y"
      by (smt (verit, ccfv_threshold) bij_betw_iff_bijections mem_Collect_eq some_eq_ex)

     ultimately show "x = y"
       using exists_g'[of "\<V>\<^sub>2 x"] someI
       unfolding f'_def get_g'_def
       by auto
   qed

   show "id ` X \<inter> f' ` Y = {}"
     using f'_not_in_x
     by auto

   show "\<forall>x\<in>X. \<V>\<^sub>1 (id x) = \<V>\<^sub>1 x"
     by simp

   show "\<forall>y\<in>Y. \<V>\<^sub>2 (f' y) = \<V>\<^sub>2 y" 
   proof(intro ballI)
     fix y
     assume "y \<in> Y"

      define g' where "g' \<equiv> SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}"

      have "y \<in> {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y}"
        by simp

      have "g' y \<in> {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}"
      proof-
        have "\<And>g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X} \<Longrightarrow>
          \<V>\<^sub>2 ((SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}) y) = \<V>\<^sub>2 y"
          "\<And>g'. \<lbrakk>bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X};
           (SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}) y \<in> X\<rbrakk>
          \<Longrightarrow> False"
          by (smt (verit, ccfv_SIG) bij_betw_apply mem_Collect_eq verit_sko_ex_indirect)+
          
        then show ?thesis
          unfolding g'_def
          using exists_g'[of "\<V>\<^sub>2 y"]
          by auto
      qed

      then show "\<V>\<^sub>2 (f' y) = \<V>\<^sub>2 y"
        unfolding g'_def f'_def get_g'_def
        by blast
   qed
qed


lemma obtain_inj''_on:
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'a :: {countable, infinite} \<Rightarrow> 'ty"
  assumes "finite X" "finite Y" "\<And>ty. infinite {x. \<V>\<^sub>1 x = ty}" "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty}"
  obtains f f' :: "'a \<Rightarrow> 'a" where
    "inj f" "inj f'"
    "f ` X \<inter> f' ` Y = {}"
    "\<forall>x \<in> X. \<V>\<^sub>1 (f x) = \<V>\<^sub>1 x"
    "\<forall>x \<in> Y. \<V>\<^sub>2 (f' x) = \<V>\<^sub>2 x"
proof-
  obtain a_to_nat :: "'a \<Rightarrow> nat" where bij_a_to_nat: "bij a_to_nat"
    using countableE_infinite[of "UNIV :: 'a set"] infinite_UNIV by blast

  define nat_to_a where "nat_to_a \<equiv> inv a_to_nat"

  have bij_nat_to_a: "bij nat_to_a"
    unfolding nat_to_a_def
    by (simp add: bij_a_to_nat bij_imp_bij_inv)

  define X_nat Y_nat where 
    "X_nat \<equiv> a_to_nat ` X" and 
    "Y_nat \<equiv> a_to_nat ` Y"

  have finite_X_nat: "finite X_nat" and finite_Y_nat: "finite Y_nat"
    unfolding X_nat_def Y_nat_def
    using assms(1,2)
    by blast+

  define \<V>\<^sub>1_nat \<V>\<^sub>2_nat where 
    "\<And>n. \<V>\<^sub>1_nat n \<equiv> \<V>\<^sub>1 (nat_to_a n)" and 
    "\<And>n. \<V>\<^sub>2_nat n \<equiv> \<V>\<^sub>2 (nat_to_a n)"

  have 
    "\<And>ty. {x. \<V>\<^sub>1_nat x = ty} = a_to_nat ` {x. \<V>\<^sub>1 x = ty}" 
    "\<And>ty. {x. \<V>\<^sub>2_nat x = ty} = a_to_nat ` {x. \<V>\<^sub>2 x = ty}"
    unfolding \<V>\<^sub>1_nat_def \<V>\<^sub>2_nat_def
    using bij_a_to_nat bij_image_Collect_eq nat_to_a_def by fastforce+

  then have \<V>_nat_infinite: "\<And>ty. infinite {x. \<V>\<^sub>1_nat x = ty}" "\<And>ty. infinite {x. \<V>\<^sub>2_nat x = ty}"
    using assms(3, 4)
    by (metis bij_a_to_nat bij_betw_finite bij_betw_subset subset_UNIV)+

  obtain f_nat f'_nat where
    inj: "inj f_nat" "inj f'_nat"  and
    disjoint: "f_nat ` X_nat \<inter> f'_nat ` Y_nat = {}"  and
    type_preserving: 
      "\<forall>x\<in> X_nat. \<V>\<^sub>1_nat (f_nat x) = \<V>\<^sub>1_nat x" 
      "\<forall>x\<in> Y_nat. \<V>\<^sub>2_nat (f'_nat x) = \<V>\<^sub>2_nat x"
    using obtain_inj_test'_on[OF finite_X_nat finite_Y_nat \<V>_nat_infinite].

  let ?f = "nat_to_a \<circ> f_nat \<circ> a_to_nat"
  let ?f' = "nat_to_a \<circ> f'_nat \<circ> a_to_nat"
  
  have "inj ?f" "inj ?f'"
    using inj
    by (simp_all add: bij_a_to_nat bij_is_inj bij_nat_to_a inj_compose)

  moreover have "?f ` X \<inter> ?f' ` Y = {}"
    using disjoint
    unfolding X_nat_def Y_nat_def
    by (metis bij_is_inj bij_nat_to_a image_Int image_comp image_empty)

  moreover have 
    "\<forall>x\<in> X. \<V>\<^sub>1 (?f x) = \<V>\<^sub>1 x" 
    "\<forall>x\<in> Y. \<V>\<^sub>2 (?f' x) = \<V>\<^sub>2 x"
    using type_preserving
    unfolding X_nat_def Y_nat_def \<V>\<^sub>1_nat_def \<V>\<^sub>2_nat_def
    by (simp_all add: bij_a_to_nat bij_is_inj nat_to_a_def)

  ultimately show ?thesis
    using that
    by presburger    
qed
   

lemma obtain_inj': 
  obtains f :: "'a :: infinite \<Rightarrow> 'a" where
    "inj f"
    "|range f| =o |UNIV - range f|"
proof-
  obtain X Y :: "'a set" where
    X_Y: 
      "|X| =o |Y|"
      "|X| =o |UNIV :: 'a set|" 
      "X \<inter> Y = {}" 
      "X \<union> Y = UNIV"
    using partitions[OF infinite_UNIV]
    by blast
    
  then obtain f where 
    f: "bij_betw f (UNIV :: 'a set) Y"
    by (meson card_of_ordIso ordIso_symmetric ordIso_transitive)

  have inj_f: "inj f" 
    using f bij_betw_def by blast+

  have Y: "Y = range f" 
    using f
    by (simp add: bij_betw_def)

  have X: "X = UNIV - range f"
    using X_Y
    unfolding Y
    by auto

  show ?thesis
    using X X_Y(1) Y inj_f ordIso_symmetric that by blast
qed

lemma obtain_inj: 
  fixes X
  defines "Y \<equiv> UNIV - X"
  assumes 
    infinite_X: "infinite X" and
    infinite_Y: "infinite Y"
  obtains f :: "'a :: {countable, infinite} \<Rightarrow> 'a" where
    "inj f"
    "range f \<inter> X = {}"
    "range f \<union> X = UNIV"
proof-
  obtain g :: "'a \<Rightarrow> nat" where bij: "bij g"
    using countableE_infinite[of "UNIV :: 'a set"] infinite_UNIV by blast

  have X_Y: "X \<inter> Y = {}" "X \<union> Y = UNIV"
    unfolding Y_def 
    by simp_all              

  have countable_X: "countable X" and countable_Y: "countable Y"
    by auto

  obtain f where 
    f: "bij_betw f (UNIV :: 'a set) Y"
    using countable_infiniteE'[OF countable_Y infinite_Y]     
    by (meson bij bij_betw_trans)

  have "inj f" 
    using f bij_betw_def by blast+

  moreover have "range f = Y" 
    using f
    by (simp_all add: bij_betw_def)

  then have "range f \<inter> X = {}" "range f \<union> X = UNIV"
    using X_Y
    by auto

  ultimately show ?thesis
    using that
    by presburger
qed

lemma obtain_injs:
  obtains f f' :: "'a :: {countable, infinite} \<Rightarrow> 'a" where
    "inj f" "inj f'" 
    "range f \<inter> range f' = {}"
    "range f \<union> range f' = UNIV"  
proof-
  obtain g :: "'a \<Rightarrow> nat" where "bij g"
    using countableE_infinite[of "UNIV :: 'a set"] infinite_UNIV by blast

  define g' where "g' \<equiv> inv g"

  then have bij_g': "bij g'"
    by (simp add: \<open>bij g\<close> bij_betw_inv_into)

  obtain X Y :: "'a set" where
    X_Y: "X \<inter> Y = {}" "X \<union> Y = UNIV" and
    infinite_X: "infinite X" and
    infinite_Y: "infinite Y"
    using obtain_infinite_partition
    by auto

  have countable_X: "countable X" and countable_Y: "countable Y"
    by blast+

  obtain f where 
    f: "bij_betw f (UNIV :: 'a set) X"
    using countable_infiniteE'[OF countable_X infinite_X]     
    by (meson \<open>bij g\<close> bij_betw_trans)

  obtain f' where 
    f': "bij_betw f' (UNIV :: 'a set) Y"
    using countable_infiniteE'[OF countable_Y infinite_Y]
    by (meson \<open>bij g\<close> bij_betw_trans)

  have "inj f" "inj f'"
    using f f' bij_betw_def by blast+

  moreover have "range f = X" "range f' = Y"
    using f f'
    by (simp_all add: bij_betw_def)

  then have "range f \<inter> range f' = {}" "range f \<union> range f' = UNIV"
    using X_Y
    by simp_all

  ultimately show ?thesis
    using that
    by presburger
qed

lemma welltyped_on_renaming_exists':
  assumes "finite X" "finite Y"  "\<And>ty. infinite {x. \<V>\<^sub>1 x = ty}" "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty}"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 :: "('f, 'v :: infinite) subst" where
    "term_subst.is_renaming \<rho>\<^sub>1" 
    "term_subst.is_renaming \<rho>\<^sub>2" 
    "\<rho>\<^sub>1 ` X \<inter> \<rho>\<^sub>2 ` Y = {}"
    "welltyped\<^sub>\<sigma>_on X \<F> \<V>\<^sub>1 \<rho>\<^sub>1"
    "welltyped\<^sub>\<sigma>_on Y \<F> \<V>\<^sub>2 \<rho>\<^sub>2"
proof-
  obtain renaming\<^sub>1 renaming\<^sub>2 :: "'v \<Rightarrow> 'v" where
    renamings:
    "inj renaming\<^sub>1" "inj renaming\<^sub>2"
    "renaming\<^sub>1 ` X \<inter> renaming\<^sub>2 ` Y = {}" 
    "\<forall>x \<in> X. \<V>\<^sub>1 (renaming\<^sub>1 x) = \<V>\<^sub>1 x" 
    "\<forall>x \<in> Y. \<V>\<^sub>2 (renaming\<^sub>2 x) = \<V>\<^sub>2 x"
    using obtain_inj''_on'[OF assms].

  define \<rho>\<^sub>1 :: "('f, 'v) subst" where
    "\<And>x. \<rho>\<^sub>1 x \<equiv> Var (renaming\<^sub>1 x)"

  define \<rho>\<^sub>2 :: "('f, 'v) subst" where
    "\<And>x. \<rho>\<^sub>2 x \<equiv> Var (renaming\<^sub>2 x)"

  have "term_subst.is_renaming \<rho>\<^sub>1"  "term_subst.is_renaming \<rho>\<^sub>2" 
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def
    using renamings(1,2)
    by (meson injD injI term_subst.is_renaming_id_subst term_subst_is_renaming_iff)+

  moreover have "\<rho>\<^sub>1 ` X \<inter> \<rho>\<^sub>2 ` Y = {}"
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def range_vars'_def
    using renamings(3)
    by auto
 
  moreover have "welltyped\<^sub>\<sigma>_on X \<F> \<V>\<^sub>1 \<rho>\<^sub>1" "welltyped\<^sub>\<sigma>_on Y \<F> \<V>\<^sub>2 \<rho>\<^sub>2"
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def welltyped\<^sub>\<sigma>_on_def
    using renamings(4, 5)
    by(auto simp: welltyped.Var)

  ultimately show ?thesis 
    using that
    by presburger
qed

lemma welltyped_on_renaming_exists:
  assumes "finite X" "finite Y"  "\<And>ty. infinite {x. \<V>\<^sub>1 x = ty}" "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty}"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 :: "('f, 'v :: {countable, infinite}) subst" where
    "term_subst.is_renaming \<rho>\<^sub>1" 
    "term_subst.is_renaming \<rho>\<^sub>2" 
    "\<rho>\<^sub>1 ` X \<inter> \<rho>\<^sub>2 ` Y = {}"
    "welltyped\<^sub>\<sigma>_on X \<F> \<V>\<^sub>1 \<rho>\<^sub>1"
    "welltyped\<^sub>\<sigma>_on Y \<F> \<V>\<^sub>2 \<rho>\<^sub>2"
proof-
  obtain renaming\<^sub>1 renaming\<^sub>2 :: "'v \<Rightarrow> 'v" where
    renamings:
    "inj renaming\<^sub>1" "inj renaming\<^sub>2"
    "renaming\<^sub>1 ` X \<inter> renaming\<^sub>2 ` Y = {}" 
    "\<forall>x \<in> X. \<V>\<^sub>1 (renaming\<^sub>1 x) = \<V>\<^sub>1 x" 
    "\<forall>x \<in> Y. \<V>\<^sub>2 (renaming\<^sub>2 x) = \<V>\<^sub>2 x"
    using obtain_inj''_on[OF assms].

  define \<rho>\<^sub>1 :: "('f, 'v) subst" where
    "\<And>x. \<rho>\<^sub>1 x \<equiv> Var (renaming\<^sub>1 x)"

  define \<rho>\<^sub>2 :: "('f, 'v) subst" where
    "\<And>x. \<rho>\<^sub>2 x \<equiv> Var (renaming\<^sub>2 x)"

  have "term_subst.is_renaming \<rho>\<^sub>1"  "term_subst.is_renaming \<rho>\<^sub>2" 
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def
    using renamings(1,2)
    by (meson injD injI term_subst.is_renaming_id_subst term_subst_is_renaming_iff)+

  moreover have "\<rho>\<^sub>1 ` X \<inter> \<rho>\<^sub>2 ` Y = {}"
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def range_vars'_def
    using renamings(3)
    by auto
 
  moreover have "welltyped\<^sub>\<sigma>_on X \<F> \<V>\<^sub>1 \<rho>\<^sub>1" "welltyped\<^sub>\<sigma>_on Y \<F> \<V>\<^sub>2 \<rho>\<^sub>2"
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def welltyped\<^sub>\<sigma>_on_def
    using renamings(4, 5)
    by(auto simp: welltyped.Var)

  ultimately show ?thesis 
    using that
    by presburger
qed

lemma welltyped\<^sub>\<sigma>_subst_upd:
  assumes "welltyped \<F> \<V> (Var var) \<tau>" "welltyped \<F> \<V> update \<tau>"  "welltyped\<^sub>\<sigma> \<F> \<V> \<gamma>" 
  shows "welltyped\<^sub>\<sigma> \<F> \<V> (\<gamma>(var := update))"
  using assms
  unfolding welltyped\<^sub>\<sigma>_def
  by (metis fun_upd_other fun_upd_same right_unique_def welltyped.Var welltyped_right_unique)

lemma welltyped\<^sub>\<sigma>_on_subst_upd:
  assumes "welltyped \<F> \<V> (Var var) \<tau>" "welltyped \<F> \<V> update \<tau>"  "welltyped\<^sub>\<sigma>_on X \<F> \<V> \<gamma>" 
  shows "welltyped\<^sub>\<sigma>_on X \<F> \<V> (\<gamma>(var := update))"
  using assms
  unfolding welltyped\<^sub>\<sigma>_on_def
  by (metis fun_upd_other fun_upd_same right_unique_def welltyped.Var welltyped_right_unique)

lemma welltyped_is_ground:
  assumes "term.is_ground t" "welltyped \<F> \<V> t \<tau>"
  shows "welltyped \<F> \<V>' t \<tau>"
  by (metis assms(1) assms(2) empty_iff welltyped_\<V>)

lemma term_subst_is_imgu_is_mgu: "term_subst.is_imgu \<mu> {{s, t}} = is_imgu \<mu> {(s, t)}"
  apply (simp add: term_subst_is_imgu_iff_is_imgu)
  by (smt (verit, ccfv_threshold) insert_absorb2 insert_commute is_imgu_def unifiers_insert_ident
      unifiers_insert_swap)

lemma the_mgu_term_subst_is_imgu:
  fixes \<sigma> :: "('f, 'v) subst"
  assumes "s \<cdot>t \<sigma> = t \<cdot>t \<sigma>"
  shows "term_subst.is_imgu (the_mgu s t) {{s, t}}"
  using term_subst_is_imgu_is_mgu the_mgu_is_imgu
  using assms by blast

lemma Fun_arg_types:
  assumes 
    "welltyped \<F> \<V> (Fun f fs) \<tau>" 
    "welltyped \<F> \<V> (Fun f gs) \<tau>" 
  obtains \<tau>s where 
    "\<F> f = (\<tau>s, \<tau>)" 
    "list_all2 (welltyped \<F> \<V>) fs \<tau>s"
    "list_all2 (welltyped \<F> \<V>) gs \<tau>s"
  by (smt (verit, ccfv_SIG) Pair_inject assms(1) assms(2) option.inject term.distinct(1) term.inject(2) welltyped.simps)

lemma welltyped_zip_option:
  assumes 
    "welltyped \<F> \<V> (Fun f ts) \<tau>" 
    "welltyped \<F> \<V> (Fun f ss) \<tau>" 
    "zip_option ts ss = Some ds" 
  shows 
    "\<forall>(a, b) \<in> set ds. \<exists>\<tau>. welltyped \<F> \<V> a \<tau> \<and> welltyped \<F> \<V> b \<tau>"
proof-

  obtain \<tau>s where 
    "list_all2 (welltyped \<F> \<V>) ts \<tau>s"
    "list_all2 (welltyped \<F> \<V>) ss \<tau>s"
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

    moreover have "list_all2 (welltyped \<F> \<V>) ts \<tau>s'" 
      using Cons_Cons.prems(2) \<tau>s by blast

    moreover have "list_all2 (welltyped \<F> \<V>) ss \<tau>s'"
      using Cons_Cons.prems(3) \<tau>s by blast

    ultimately have "\<forall>(t, s)\<in>set ds'. \<exists>\<tau>. welltyped \<F> \<V> t \<tau> \<and> welltyped \<F> \<V> s \<tau>"
      using Cons_Cons.IH
      by presburger

    moreover have "\<exists>\<tau>. welltyped \<F> \<V> t \<tau> \<and> welltyped \<F> \<V> s \<tau>"
      using Cons_Cons.prems(2) Cons_Cons.prems(3) \<tau>s by blast

    ultimately show ?case
      using Cons_Cons.prems(1) ds
      by fastforce
  qed(auto)
qed

lemma welltyped_decompose':
  assumes
    "welltyped \<F> \<V> (Fun f fs) \<tau>" 
    "welltyped \<F> \<V> (Fun f gs) \<tau>"
    "decompose (Fun f fs) (Fun g gs) = Some ds"
  shows "\<forall>(t, t') \<in> set ds. \<exists>\<tau>. welltyped \<F> \<V> t \<tau> \<and> welltyped \<F> \<V> t' \<tau>"
  using assms welltyped_zip_option[OF assms(1,2)]
  by force

lemma welltyped_decompose:
  assumes
    "welltyped \<F> \<V> f \<tau>" 
    "welltyped \<F> \<V> g \<tau>"
    "decompose f g = Some ds"
  shows "\<forall>(t, t') \<in> set ds. \<exists>\<tau>. welltyped \<F> \<V> t \<tau> \<and> welltyped \<F> \<V> t' \<tau>"
proof-

  obtain f' fs gs where "f = Fun f' fs" "g = Fun f' gs"
    using assms(3)
    unfolding decompose_def
    by (smt (z3) option.distinct(1) prod.simps(2) rel_option_None1 term.split_sels(2))

  then show ?thesis
    using assms welltyped_decompose'
    by (metis (mono_tags, lifting))
qed

lemma welltyped_subst'_subst: 
  assumes "welltyped \<F> \<V> (Var x) \<tau>" "welltyped \<F> \<V> t \<tau>"
  shows "welltyped\<^sub>\<sigma> \<F> \<V> (subst x t)"
  using assms
  unfolding subst_def welltyped\<^sub>\<sigma>_def
  by (simp add: welltyped.simps)

lemma welltyped_unify:
  assumes    
    "unify es bs = Some unifier"
    "\<forall>(t, t') \<in> set es. \<exists>\<tau>. welltyped \<F> \<V> t \<tau> \<and> welltyped \<F> \<V> t' \<tau>"
    "welltyped\<^sub>\<sigma> \<F> \<V> (subst_of bs)"
  shows "welltyped\<^sub>\<sigma> \<F> \<V> (subst_of unifier)"
  using assms
proof(induction es bs arbitrary: unifier rule: unify.induct)
  case (1 bs)
  then show ?case
    by simp
next
  case (2 f ss g ts E bs)
  then obtain \<tau> where \<tau>:
    "welltyped \<F> \<V> (Fun f ss) \<tau>" 
    "welltyped \<F> \<V> (Fun g ts) \<tau>"
    by auto

  obtain ds where ds: "decompose (Fun f ss) (Fun g ts) = Some ds"
    using 2(2)
    by(simp split: option.splits)

  moreover then have "unify (ds @ E) bs = Some unifier"
    using "2.prems"(1) by auto

  moreover have "\<forall>(t, t')\<in>set (ds @ E). \<exists>\<tau>. welltyped \<F> \<V> t \<tau> \<and> welltyped \<F> \<V> t' \<tau>"
    using welltyped_decompose[OF \<tau> ds] 2(3)
    by fastforce

  ultimately show ?case 
    using 2
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
      "\<forall>(s, s') \<in> set E. \<exists>\<tau>. welltyped \<F> \<V> (s \<cdot>t Var(x := t)) \<tau> \<and> welltyped \<F> \<V> (s' \<cdot>t Var(x := t)) \<tau>"
      using 3(4)
      by (smt (verit, ccfv_threshold) case_prodD case_prodI2 fun_upd_apply welltyped.Var 
          list.set_intros(1) list.set_intros(2) right_uniqueD welltyped_right_unique 
          welltyped\<^sub>\<sigma>_def welltyped\<^sub>\<sigma>_welltyped)

    moreover then have 
      "\<forall>(s, s') \<in> set (subst_list (subst x t) E). \<exists>\<tau>. welltyped \<F> \<V> s \<tau> \<and> welltyped \<F> \<V> s' \<tau>"
      unfolding subst_def subst_list_def
      by fastforce

    moreover have "welltyped\<^sub>\<sigma> \<F> \<V> (subst x t)"
      using 3(4) welltyped_subst'_subst
      by fastforce

    moreover then have "welltyped\<^sub>\<sigma> \<F> \<V> (subst_of ((x, t) # bs))"
      using 3(5)
      unfolding welltyped\<^sub>\<sigma>_def
      by (simp add: calculation(4) subst_compose_def welltyped\<^sub>\<sigma>_welltyped)

    ultimately show ?thesis 
      using 3(2, 3) False by force
  qed
next
  case (4 t ts x E bs)
  then have "unify (subst_list (subst x (Fun t ts)) E) ((x, (Fun t ts)) # bs) = Some unifier"
    by(auto split: if_splits)

  moreover have 
    "\<forall>(s, s') \<in> set E. \<exists>\<tau>. 
        welltyped \<F> \<V> (s \<cdot>t Var(x := (Fun t ts))) \<tau> \<and> welltyped \<F> \<V> (s' \<cdot>t Var(x := (Fun t ts))) \<tau>"
    using 4(3)
    by (smt (verit, ccfv_threshold) case_prodD case_prodI2 fun_upd_apply welltyped.Var 
        list.set_intros(1) list.set_intros(2) right_uniqueD welltyped_right_unique 
        welltyped\<^sub>\<sigma>_def welltyped\<^sub>\<sigma>_welltyped)

  moreover then have 
    "\<forall>(s, s') \<in> set (subst_list (subst x (Fun t ts)) E). \<exists>\<tau>. 
        welltyped \<F> \<V> s \<tau> \<and> welltyped \<F> \<V> s' \<tau>"
    unfolding subst_def subst_list_def
    by fastforce

  moreover have "welltyped\<^sub>\<sigma> \<F> \<V> (subst x (Fun t ts))"
    using 4(3) welltyped_subst'_subst
    by fastforce

  moreover then have "welltyped\<^sub>\<sigma> \<F> \<V> (subst_of ((x, (Fun t ts)) # bs))"
    using 4(4) 
    unfolding welltyped\<^sub>\<sigma>_def
    by (simp add: calculation(4) subst_compose_def welltyped\<^sub>\<sigma>_welltyped)

  ultimately show ?case 
    using 4(1, 2)
    by (metis (no_types, lifting) option.distinct(1) unify.simps(4))
qed

lemma welltyped_unify':
  assumes 
    unify: "unify [(t, t')] [] = Some unifier" and
    \<tau>: "\<exists>\<tau>. welltyped \<F> \<V> t \<tau> \<and> welltyped \<F> \<V> t' \<tau>"
  shows "welltyped\<^sub>\<sigma> \<F> \<V> (subst_of unifier)"
  using assms welltyped_unify[OF unify] \<tau> welltyped\<^sub>\<sigma>_Var
  by fastforce

lemma welltyped_the_mgu: 
  assumes
    the_mgu: "the_mgu t t' = \<mu>" and
    \<tau>: "\<exists>\<tau>. welltyped \<F> \<V> t \<tau> \<and> welltyped \<F> \<V> t' \<tau>"
  shows 
    "welltyped\<^sub>\<sigma> \<F> \<V> \<mu>"
  using assms welltyped_unify'[of t t' _ \<F> \<V>]
  unfolding the_mgu_def mgu_def welltyped\<^sub>\<sigma>_def 
  by(auto simp: welltyped.Var split: option.splits)

abbreviation welltyped_imgu where
  "welltyped_imgu \<F> \<V> term term' \<mu> \<equiv>
    \<forall>\<tau>. welltyped \<F> \<V> term \<tau> \<longrightarrow> welltyped \<F> \<V> term' \<tau> \<longrightarrow> welltyped\<^sub>\<sigma> \<F> \<V> \<mu>"

lemma welltyped_imgu_exists:
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes unified: "term \<cdot>t \<upsilon> = term' \<cdot>t \<upsilon>"
  obtains \<mu> :: "('f, 'v) subst"
  where 
    "\<upsilon> = \<mu> \<odot> \<upsilon>" 
    "term_subst.is_imgu \<mu> {{term, term'}}"
    "welltyped_imgu \<F> \<V> term term' \<mu>"
proof-
  obtain \<mu> where \<mu>: "the_mgu term term' = \<mu>"
    using assms ex_mgu_if_subst_apply_term_eq_subst_apply_term by blast

  have "welltyped_imgu \<F> \<V> term term' (the_mgu term term')"
    using welltyped_the_mgu[OF \<mu>, of \<F> \<V>] assms
    unfolding \<mu>
    by blast

  then show ?thesis
    using that imgu_exists_extendable[OF unified]
    by (metis the_mgu the_mgu_term_subst_is_imgu unified)
qed

abbreviation welltyped_imgu' where
  "welltyped_imgu' \<F> \<V> term term' \<mu> \<equiv>
    \<exists>\<tau>. welltyped \<F> \<V> term \<tau> \<and> welltyped \<F> \<V> term' \<tau> \<and> welltyped\<^sub>\<sigma> \<F> \<V> \<mu>"

lemma welltyped_imgu'_exists:
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes unified: "term \<cdot>t \<upsilon> = term' \<cdot>t \<upsilon>" and "welltyped \<F> \<V> term \<tau>" "welltyped \<F> \<V> term' \<tau>"
  obtains \<mu> :: "('f, 'v) subst"
  where 
    "\<upsilon> = \<mu> \<odot> \<upsilon>" 
    "term_subst.is_imgu \<mu> {{term, term'}}"
    "welltyped_imgu' \<F> \<V> term term' \<mu>"
proof-
  obtain \<mu> where \<mu>: "the_mgu term term' = \<mu>"
    using assms ex_mgu_if_subst_apply_term_eq_subst_apply_term by blast

  have "welltyped_imgu \<F> \<V> term term' (the_mgu term term')"
    using welltyped_the_mgu[OF \<mu>, of \<F> \<V>] assms
    unfolding \<mu>
    by blast

  then show ?thesis
    using that imgu_exists_extendable[OF unified]
    by (metis assms(2) assms(3) the_mgu the_mgu_term_subst_is_imgu unified)
qed

end
