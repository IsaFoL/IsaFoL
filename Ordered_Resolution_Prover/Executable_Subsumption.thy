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
  by (cases l) auto

lemma subsumes_list_complete:
  "subsumes_list Ls Ks = None \<Longrightarrow> \<forall>\<rho>. \<not> mset (map (\<lambda>L. L \<cdot>lit \<rho>) Ls) \<subseteq># mset Ks"
proof (induction Ls Ks rule: subsumes_list.induct[case_names Nil Cons])
  case (Cons L Ls Ks)
  from Cons.prems show ?case
  proof (cases "find (\<lambda>K. is_pos K = is_pos L \<and> match (atm_of K) (atm_of L) \<noteq> None) Ks")
    case None
    then show ?thesis
      apply (auto simp: find_None_iff dest!: spec[of _ "L \<cdot>lit _"] match_complete) sorry
  next
    case (Some K)
    let ?\<rho> = "the (match (atm_of K) (atm_of L))"
    let ?Ks = "remove1 K Ks"
    from Cons.prems Some show ?thesis
    proof (cases "subsumes_list (map (\<lambda>L. L \<cdot>lit ?\<rho>) Ls) ?Ks")
      case None
      note IH = Cons.IH(1)[OF Some refl refl None]
      then show ?thesis
        apply (auto simp: image_image literal.map_comp o_def elim!: meta_mp)
        sorry
    qed (subst (asm) subsumes_list.simps(2), auto)
  qed
qed simp

lemma subsumes_list_sound:
  "subsumes_list Ls Ks = Some \<rho> \<Longrightarrow> mset (map (\<lambda>L. L \<cdot>lit \<rho>) Ls) \<subseteq># mset Ks"
proof (induct Ls Ks arbitrary: \<rho> rule: subsumes_list.induct[case_names Nil Cons])
  case (Cons L Ls Ks)
  then show ?case sorry
qed simp

lemma subsumes_subsumes_list[code_unfold]:
  "subsumes (mset Ls) (mset Ks) = (subsumes_list Ls Ks \<noteq> None)"
  unfolding subsumes_def using subsumes_list_sound[of Ls Ks] subsumes_list_complete[of Ls Ks]
  by (auto simp: subst_cls_def subst_lit_def)

lemma subsumes_list_subsumes:
  "(\<exists>\<sigma>. subsumes_list Ls Ks = Some \<sigma>) = subsumes (mset Ls) (mset Ks)"
  "(subsumes_list Ls Ks = None) = (\<not> subsumes (mset Ls) (mset Ks))"
  by (simp_all add: subsumes_subsumes_list)

lemma strictly_subsumes_subsumes_list[code_unfold]:
  "strictly_subsumes (mset Ls) (mset Ks) = (subsumes_list Ls Ks \<noteq> None \<and> subsumes_list Ks Ls = None)"
  unfolding strictly_subsumes_def subsumes_subsumes_list by simp

end
