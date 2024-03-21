theory Ground_Type_System
  imports Ground_Clause
begin

inductive has_type for \<F> where
  GFun: "
    \<F> f = (\<tau>s, \<tau>) \<Longrightarrow> list_all2 (has_type \<F>) ts \<tau>s \<Longrightarrow>
    has_type \<F> (GFun f ts) \<tau>"

lemma right_unique_has_type: "right_unique (has_type \<F>)"
proof (rule right_uniqueI)
  fix t \<tau>\<^sub>1 \<tau>\<^sub>2
  assume "has_type \<F> t \<tau>\<^sub>1" and "has_type \<F> t \<tau>\<^sub>2"
  thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
    by (auto elim!: has_type.cases)
qed

definition well_typed_atm where
  "well_typed_atm \<F> A \<longleftrightarrow> (\<exists>\<tau>. \<forall>t \<in> set_uprod A. has_type \<F> t \<tau>)"

definition well_typed_lit where
  "well_typed_lit \<F> L \<longleftrightarrow> well_typed_atm \<F> (atm_of L)"

definition well_typed_cls where
  "well_typed_cls \<F> C \<longleftrightarrow> (\<forall>L \<in># C. well_typed_lit \<F> L)"

definition well_typed_cls_set where
  "well_typed_cls_set \<F> N \<longleftrightarrow> (\<forall>C \<in> N. well_typed_cls \<F> C)"

lemma well_typed_cls_add_mset: "well_typed_cls \<F> (add_mset L C) \<longleftrightarrow> well_typed_lit \<F> L \<and> well_typed_cls \<F> C"
  by (simp add: well_typed_cls_def)

lemma well_typed_cls_plus: "well_typed_cls \<F> (C + D) \<longleftrightarrow> well_typed_cls \<F> C \<and> well_typed_cls \<F> D"
  by (auto simp: well_typed_cls_def)

lemma gctxt_apply_term_preserves_typing:
  assumes
    \<kappa>_type: "has_type \<F> \<kappa>\<langle>t\<rangle>\<^sub>G \<tau>\<^sub>1" and
    t_type: "has_type \<F> t \<tau>\<^sub>2" and
    t'_type: "has_type \<F> t' \<tau>\<^sub>2"
  shows "has_type \<F> \<kappa>\<langle>t'\<rangle>\<^sub>G \<tau>\<^sub>1"
  using \<kappa>_type
proof (induction \<kappa> arbitrary: \<tau>\<^sub>1)
  case GHole
  then show ?case
    using t_type t'_type
    using right_unique_has_type[of \<F>, THEN right_uniqueD]
    by auto
next
  case (GMore f ss1 \<kappa> ss2)
  have "has_type \<F> (GFun f (ss1 @ \<kappa>\<langle>t\<rangle>\<^sub>G # ss2)) \<tau>\<^sub>1"
    using GMore.prems by simp
  hence "has_type \<F> (GFun f (ss1 @ \<kappa>\<langle>t'\<rangle>\<^sub>G # ss2)) \<tau>\<^sub>1"
  proof (cases \<F> "GFun f (ss1 @ \<kappa>\<langle>t\<rangle>\<^sub>G # ss2)" \<tau>\<^sub>1 rule: has_type.cases)
    case (GFun \<tau>s)
    show ?thesis
    proof (rule has_type.GFun)
      show "\<F> f = (\<tau>s, \<tau>\<^sub>1)"
        using \<open>\<F> f = (\<tau>s, \<tau>\<^sub>1)\<close> .
    next
      show "list_all2 (has_type \<F>) (ss1 @ \<kappa>\<langle>t'\<rangle>\<^sub>G # ss2) \<tau>s"
        using \<open>list_all2 (has_type \<F>) (ss1 @ \<kappa>\<langle>t\<rangle>\<^sub>G # ss2) \<tau>s\<close>
        using GMore.IH
        by (smt (verit, del_insts) list_all2_Cons1 list_all2_append1 list_all2_lengthD)
    qed
  qed
  thus ?case
    by simp
qed

end