theory Substitution_HOL_ex_Unification
  imports
    Substitution
    "HOL-ex.Unification"
begin

no_notation Comb (infix "\<cdot>" 60)

quotient_type 'a subst = "('a \<times> 'a trm) list" / "(\<doteq>)"
proof (rule equivpI)
  show "reflp (\<doteq>)"
    using reflpI subst_refl by metis
next
  show "symp (\<doteq>)"
    using sympI subst_sym by metis
next
  show "transp (\<doteq>)"
    using transpI subst_trans by metis
qed

lift_definition subst_comp :: "'a subst \<Rightarrow> 'a subst \<Rightarrow> 'a subst" (infixl "\<odot>" 67)
  is Unification.comp
  using Unification.subst_cong .

definition subst_id :: "'a subst" where
  "subst_id = abs_subst []"

global_interpretation subst_comp: monoid subst_comp subst_id
proof unfold_locales
  show "\<And>a b c. a \<odot> b \<odot> c = a \<odot> (b \<odot> c)"
    by (smt (verit, del_insts) Quotient3_abs_rep Quotient3_subst Unification.comp_assoc
        subst.abs_eq_iff subst_comp.abs_eq)
next
  show "\<And>a. subst_id \<odot> a = a"
    by (metis Quotient3_abs_rep Quotient3_subst comp.simps(1) subst_comp.abs_eq subst_id_def)
next
  show "\<And>a. a \<odot> subst_id = a"
    by (metis Quotient3_abs_rep Quotient3_subst comp_Nil subst_comp.abs_eq subst_id_def)
qed

lift_definition subst_apply :: "'a trm \<Rightarrow> 'a subst \<Rightarrow> 'a trm"
  is Unification.subst
  using Unification.subst_eq_dest .

abbreviation is_ground_trm where
  "is_ground_trm t \<equiv> vars_of t = {}"

global_interpretation term_subst: substitution where
  subst = subst_apply and id_subst = subst_id and comp_subst = subst_comp and
  is_ground = is_ground_trm
proof unfold_locales
  show "\<And>x a b. subst_apply x (a \<odot> b) = subst_apply (subst_apply x a) b"
    by (metis map_fun_apply subst_apply.abs_eq subst_apply.rep_eq subst_comp subst_comp_def)
next
  show "\<And>x. subst_apply x subst_id = x"
    by (simp add: subst_apply.abs_eq subst_id_def)
next
  show "\<And>x. is_ground_trm x \<Longrightarrow> \<forall>\<sigma>. subst_apply x \<sigma> = x"
    by (metis agreement empty_iff subst_Nil subst_apply.rep_eq)
qed

end