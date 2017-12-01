(*  Title:       An Executable Algorithm for Clause Subsumption
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)


section \<open>An Executable Algorithm for Clause Subsumption\<close>

theory Executable_Subsumption
  imports
    IsaFoR_IsaFoR_Term
    "$ISAFOR/Rewriting/Matching"
begin

definition "ext_gsubst x = Fun (Inr x) []"
definition "ext_emb = map_term Inl id"

fun undo_ext where
  "undo_ext (Var x) = Var x"
| "undo_ext (Fun (Inr x) ts) = Var x"
| "undo_ext (Fun (Inl x) ts) = Fun x (map undo_ext ts)"

lemma undo_ext_gsubst_inverse[simp]:
  "undo_ext (ext_gsubst x) = Var x"
  "undo_ext (ext_emb t \<cdot> \<sigma>) = t \<cdot> (undo_ext o \<sigma>)"
  "undo_ext (ext_emb t) = t"
  by (induct t) (auto simp: ext_gsubst_def ext_emb_def cong: map_cong)

lemma subst_ext_gsubst: "t \<cdot> ext_gsubst \<cdot> \<sigma> = t \<cdot> ext_gsubst"
  by (induct t) (auto simp: ext_gsubst_def)

lemma is_ground_subst_ext_gsubst: "is_ground_subst ext_gsubst"
  unfolding is_ground_subst_def ext_gsubst_def is_ground_atm_def subst_ext_gsubst by blast

lemma ext_emb_subst[simp]: "ext_emb (t \<cdot> \<sigma>) = ext_emb t \<cdot> (ext_emb o \<sigma>)"
  by (induct t) (auto simp: ext_emb_def)

lemma subsumes_ground:
  "subsumes (map_clause ext_emb C) (map_clause ext_emb D \<cdot>cls ext_gsubst) \<longleftrightarrow> subsumes C D"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume ?R
  then obtain \<sigma> where "subst_cls C \<sigma> \<subseteq># D"
    unfolding subsumes_def by auto
  from image_mset_subseteq_mono[of _ _ "map_literal ((\<lambda>t. t \<cdot> ext_gsubst) o ext_emb)", OF this]
  show ?L
    by (auto simp: subsumes_def multiset.map_comp literal.map_comp
     subst_cls_def subst_apply_clause_def subst_lit_def o_def subst_subst subst_compose_def)
qed (auto simp: subsumes_def multiset.map_comp literal.map_ident literal.map_comp
     subst_cls_def subst_apply_clause_def subst_lit_def o_def
     dest!: image_mset_subseteq_mono[of _ _ "map_literal undo_ext"])

context notes length_remove1[termination_simp] find_Some_iff[termination_simp] begin
fun subsumes_list where
  "subsumes_list [] Ks = Some Var"
| "subsumes_list (L # Ls) Ks =
     (case List.find (\<lambda>K. is_pos K = is_pos L \<and> match (atm_of K) (atm_of L) \<noteq> None) Ks of
       None \<Rightarrow> None
     | Some K \<Rightarrow>
         (let \<rho> = the (match (atm_of K) (atm_of L)); Ks' = remove1 K Ks in
         case subsumes_list (map (\<lambda>L. L \<cdot>lit \<rho>) Ls) Ks' of
           None \<Rightarrow> subsumes_list (L # Ls) Ks'
         | Some \<sigma> \<Rightarrow> Some (\<rho> \<circ>\<^sub>s \<sigma>)))"
end

declare subsumes_list.simps(2)[simp del]

lemma atm_of_map_literal[simp]: "atm_of (map_literal f l) = f (atm_of l)"

abbreviation subsumes_list_subst  (infixl "\<triangleleft>" 60) where
  "subsumes_list_subst Ls Ks \<equiv> subsumes (mset Ls) (mset Ks)"
term match_term_list
lemma "\<forall>K \<in> set Ks. is_ground_lit K \<Longrightarrow>
  L # Ls \<triangleleft> Ks \<longleftrightarrow> (\<exists>K \<in> set Ks. \<exists>\<rho>. L \<cdot>lit \<rho> = K \<and> map (\<lambda>L. L \<cdot>lit \<rho>) Ls \<triangleleft> remove1 K Ks)"
  unfolding subsumes_def
  apply safe
  apply (auto simp: insert_subset_eq_iff subst_lit_def subst_cls_def literal.map_ident) []
   apply (erule bexI[rotated])
   apply (rule exI conjI)+
    apply (rule refl)
   apply (rule exI[of _ Var])
   apply (auto simp: subst_cls_def subst_lit_def literal.map_ident) []
  apply (rule_tac x = "\<rho> \<circ>\<^sub>s \<sigma>" in exI)
  apply (auto simp: insert_subset_eq_iff subst_lit_def subst_cls_def
    cong: literal.map_cong split: if_splits)
  
  find_theorems "add_mset _ _ \<subseteq># _"
  sorry

lemma subsumes_list_complete:
  "subsumes_list Ls Ks = None \<Longrightarrow> \<not> Ls \<triangleleft> Ks"
  sorry
proof (induction Ls Ks rule: subsumes_list.induct[case_names Nil_Nil Cons_Nil Cons])
  case (Cons L Ls Ks)
  show ?case sorry(*
  proof
    fix \<rho>
    from Cons.prems show "\<not> mset (map (\<lambda>a. a \<cdot>lit \<rho>) (L # Ls)) \<subseteq># mset Ks"
    proof (cases "find (\<lambda>K. is_pos K = is_pos L \<and> match (atm_of K) (atm_of L) \<noteq> None) Ks")
      case None
      then show ?thesis
        by (auto simp: find_None_iff dest!: spec[of _ "L \<cdot>lit \<rho>"] match_complete)
    next
      case (Some K)
      let ?\<rho>KL = "the (match (atm_of K) (atm_of L))"
      let ?Ks = "remove1 K Ks"
      from Cons.prems Some show ?thesis
      proof (cases "subsumes_list (map (\<lambda>L. L \<cdot>lit ?\<rho>KL) Ls) ?Ks")
        case None
        with Cons.prems Some have "subsumes_list (L # Ls) ?Ks = None"
          by (subst (asm) subsumes_list.simps(2)) (auto simp: Let_def)
        note IH =
          Cons.IH(1)[OF Some refl refl None, THEN spec, of \<rho>]
          Cons.IH(2)[OF Some refl refl None this, THEN spec, of \<rho>]
        with Some None show ?thesis
          apply (auto simp: literal.map_comp o_def insert_subset_eq_iff is_pos_def
            find_Some_iff subst_subst simp del: subst_subst_compose dest!: match_sound spec[of _ "\<rho>"])
          sledgehammer
          subgoal for i \<sigma> t
           apply (drule spec[of _ "\<rho>"])
            apply (erule notE)
            apply auto
          find_theorems "add_mset _ _ \<subseteq># _"
          sorry
        sorry
      qed (subst (asm) subsumes_list.simps(2), auto)
    qed
  qed*)
qed simp

lemma subsumes_list_sound:
  "subsumes_list Ls Ks = Some \<rho> \<Longrightarrow> mset (map (\<lambda>L. L \<cdot>lit \<rho>) Ls) \<subseteq># mset Ks"
  sorry
(*
proof (induct Ls Ks arbitrary: \<rho> rule: subsumes_list.induct[case_names Nil Cons])
  case (Cons L Ls Ks)
  then show ?case sorry
qed simp
*)

lemma subsumes_subsumes_list[code_unfold]:
  "subsumes (mset Ls) (mset Ks) = (subsumes_list Ls Ks \<noteq> None)"
  using subsumes_list_sound[of Ls Ks] subsumes_list_complete[of Ls Ks]
  by (auto simp: subst_cls_def subst_lit_def subsumes_def)

lemma subsumes_list_subsumes:
  "(\<exists>\<sigma>. subsumes_list Ls Ks = Some \<sigma>) = subsumes (mset Ls) (mset Ks)"
  "(subsumes_list Ls Ks = None) = (\<not> subsumes (mset Ls) (mset Ks))"
  by (simp_all add: subsumes_subsumes_list)

lemma strictly_subsumes_subsumes_list[code_unfold]:
  "strictly_subsumes (mset Ls) (mset Ks) = (subsumes_list Ls Ks \<noteq> None \<and> subsumes_list Ks Ls = None)"
  unfolding strictly_subsumes_def subsumes_subsumes_list by simp

end