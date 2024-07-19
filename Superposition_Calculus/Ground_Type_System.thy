theory Ground_Type_System
  imports Ground_Clause
begin

inductive welltyped for \<F> where
  GFun: "\<F> f = (\<tau>s, \<tau>) \<Longrightarrow> list_all2 (welltyped \<F>) ts \<tau>s \<Longrightarrow> welltyped \<F> (GFun f ts) \<tau>"

lemma welltyped_right_unique: "right_unique (welltyped \<F>)"
proof (rule right_uniqueI)
  fix t \<tau>\<^sub>1 \<tau>\<^sub>2
  assume "welltyped \<F> t \<tau>\<^sub>1" and "welltyped \<F> t \<tau>\<^sub>2"
  thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
    by (auto elim!: welltyped.cases)
qed

definition welltyped\<^sub>a where
  "welltyped\<^sub>a \<F> A \<longleftrightarrow> (\<exists>\<tau>. \<forall>t \<in> set_uprod A. welltyped \<F> t \<tau>)"

definition welltyped\<^sub>l where
  "welltyped\<^sub>l \<F> L \<longleftrightarrow> welltyped\<^sub>a \<F> (atm_of L)"

definition welltyped\<^sub>c where
  "welltyped\<^sub>c \<F> C \<longleftrightarrow> (\<forall>L \<in># C. welltyped\<^sub>l \<F> L)"

definition welltyped\<^sub>c\<^sub>s where
  "welltyped\<^sub>c\<^sub>s \<F> N \<longleftrightarrow> (\<forall>C \<in> N. welltyped\<^sub>c \<F> C)"

lemma welltyped\<^sub>c_add_mset: 
  "welltyped\<^sub>c \<F> (add_mset L C) \<longleftrightarrow> welltyped\<^sub>l \<F> L \<and> welltyped\<^sub>c \<F> C"
  by (simp add: welltyped\<^sub>c_def)

lemma welltyped\<^sub>c_plus: 
  "welltyped\<^sub>c \<F> (C + D) \<longleftrightarrow> welltyped\<^sub>c \<F> C \<and> welltyped\<^sub>c \<F> D"
  by (auto simp: welltyped\<^sub>c_def)

lemma gctxt_apply_term_preserves_typing:
  assumes
    \<kappa>_type: "welltyped \<F> \<kappa>\<langle>t\<rangle>\<^sub>G \<tau>\<^sub>1" and
    t_type: "welltyped \<F> t \<tau>\<^sub>2" and
    t'_type: "welltyped \<F> t' \<tau>\<^sub>2"
  shows "welltyped \<F> \<kappa>\<langle>t'\<rangle>\<^sub>G \<tau>\<^sub>1"
  using \<kappa>_type
proof (induction \<kappa> arbitrary: \<tau>\<^sub>1)
  case GHole
  then show ?case
    using t_type t'_type
    using welltyped_right_unique[of \<F>, THEN right_uniqueD]
    by auto
next
  case (GMore f ss1 \<kappa> ss2)
  have "welltyped \<F> (GFun f (ss1 @ \<kappa>\<langle>t\<rangle>\<^sub>G # ss2)) \<tau>\<^sub>1"
    using GMore.prems by simp
  hence "welltyped \<F> (GFun f (ss1 @ \<kappa>\<langle>t'\<rangle>\<^sub>G # ss2)) \<tau>\<^sub>1"
  proof (cases \<F> "GFun f (ss1 @ \<kappa>\<langle>t\<rangle>\<^sub>G # ss2)" \<tau>\<^sub>1 rule: welltyped.cases)
    case (GFun \<tau>s)
    show ?thesis
    proof (rule welltyped.GFun)
      show "\<F> f = (\<tau>s, \<tau>\<^sub>1)"
        using \<open>\<F> f = (\<tau>s, \<tau>\<^sub>1)\<close> .
    next
      show "list_all2 (welltyped \<F>) (ss1 @ \<kappa>\<langle>t'\<rangle>\<^sub>G # ss2) \<tau>s"
        using \<open>list_all2 (welltyped \<F>) (ss1 @ \<kappa>\<langle>t\<rangle>\<^sub>G # ss2) \<tau>s\<close>
        using GMore.IH
        by (smt (verit, del_insts) list_all2_Cons1 list_all2_append1 list_all2_lengthD)
    qed
  qed
  thus ?case
    by simp
qed

end