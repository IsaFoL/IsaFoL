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
  "subsumes_list [] Ks \<sigma> = True"
| "subsumes_list (L # Ls) Ks \<sigma> =
     (case List.find (\<lambda>K. is_pos K = is_pos L \<and> match_term_list [(atm_of L, atm_of K)] \<sigma> \<noteq> None) Ks of
       None \<Rightarrow> False
     | Some K \<Rightarrow>
         (let \<rho> = the (match_term_list [(atm_of L, atm_of L)] \<sigma>); Ks' = remove1 K Ks in
         subsumes_list Ls Ks' \<rho> \<or> subsumes_list (L # Ls) Ks' \<rho>))"
end

declare subsumes_list.simps(2)[simp del]

lemma atm_of_map_literal[simp]: "atm_of (map_literal f l) = f (atm_of l)"
  by (cases l; simp)

definition "extends_subst \<sigma> \<tau> = (\<forall>x \<in> dom \<sigma>. \<sigma> x = \<tau> x)"

lemma extends_subst_refl: "extends_subst \<sigma> \<sigma>"
  unfolding extends_subst_def by auto

lemma extends_subst_trans: "extends_subst \<sigma> \<tau> \<Longrightarrow> extends_subst \<tau> \<rho> \<Longrightarrow> extends_subst \<sigma> \<rho>"
  unfolding extends_subst_def dom_def by (metis mem_Collect_eq)

lemma extends_subst_dom: "extends_subst \<sigma> \<tau> \<Longrightarrow> dom \<sigma> \<subseteq> dom \<tau>"
  unfolding extends_subst_def dom_def by auto

lemma exteinds_subst_fun_upd_new: 
  "\<sigma> x = None \<Longrightarrow> extends_subst (\<sigma>(x \<mapsto> t)) \<tau> \<longleftrightarrow> extends_subst \<sigma> \<tau> \<and> \<tau> x = Some t"
  unfolding extends_subst_def dom_fun_upd subst_of_map_def
  by (force simp add: dom_def split: option.splits)

lemma exteinds_subst_fun_upd_matching:
  "\<sigma> x = Some t \<Longrightarrow> extends_subst (\<sigma>(x \<mapsto> t)) \<tau> \<longleftrightarrow> extends_subst \<sigma> \<tau>"
  unfolding extends_subst_def dom_fun_upd subst_of_map_def
  by (auto simp add: dom_def split: option.splits)

lemma extends_subst_empty: "extends_subst Map.empty \<tau>"
  unfolding extends_subst_def by auto

lemma extends_subst_cong_term:
  "extends_subst \<sigma> \<tau> \<Longrightarrow> vars_term t \<subseteq> dom \<sigma> \<Longrightarrow> t \<cdot> subst_of_map Var \<sigma> = t \<cdot> subst_of_map Var \<tau>"
  by (force simp: extends_subst_def subst_of_map_def split: option.splits intro!: term_subst_eq)

lemma extends_subst_cong_lit:
  "extends_subst \<sigma> \<tau> \<Longrightarrow> vars_lit L \<subseteq> dom \<sigma> \<Longrightarrow> L \<cdot>lit subst_of_map Var \<sigma> = L \<cdot>lit subst_of_map Var \<tau>"
  by (cases L) (auto simp: extends_subst_cong_term)

definition "subsumes_modulo C D \<sigma> =
   (\<exists>\<tau>. vars_clause C \<subseteq> dom \<tau> \<and> extends_subst \<sigma> \<tau> \<and> subst_cls C (subst_of_map Var \<tau>) \<subseteq># D)"

abbreviation subsumes_list_modulo where
  "subsumes_list_modulo Ls Ks \<sigma> \<equiv> subsumes_modulo (mset Ls) (mset Ks) \<sigma>"

lemma vars_clause_add_mset[simp]: "vars_clause (add_mset L C) = vars_lit L \<union> vars_clause C"
  unfolding vars_clause_def by auto

lemma subsumes_list_modulo_Cons: "subsumes_list_modulo (L # Ls) Ks \<sigma> \<longleftrightarrow>
  (\<exists>K \<in> set Ks. \<exists>\<tau>. extends_subst \<sigma> \<tau> \<and> vars_lit L \<subseteq> dom \<tau> \<and> L \<cdot>lit (subst_of_map Var \<tau>) = K
     \<and> subsumes_list_modulo Ls (remove1 K Ks) \<tau>)"
  unfolding subsumes_modulo_def
  apply safe
   apply (auto simp: insert_subset_eq_iff subst_lit_def subst_cls_def literal.map_ident
     intro: extends_subst_refl extends_subst_trans)
  apply (intro exI conjI)
      prefer 3
      apply (rule extends_subst_trans; assumption)
     apply (erule (1) order_trans[OF _ extends_subst_dom])
    apply assumption
  apply (auto simp: extends_subst_cong_lit)
  done

lemma match_term_list_sound: "match_term_list tus \<sigma> = Some \<tau> \<Longrightarrow>
  (\<Union>(t, u)\<in>set tus. vars_term t) \<subseteq> dom \<tau> \<and> extends_subst \<sigma> \<tau> \<and> (\<forall>(t,u)\<in>set tus. t \<cdot> subst_of_map Var \<tau> = u)"
  apply (induct tus \<sigma> arbitrary: \<tau> rule: match_term_list.induct)
     apply (auto simp: extends_subst_refl exteinds_subst_fun_upd_new exteinds_subst_fun_upd_matching
      subst_of_map_def split: if_splits option.splits
      cong: list.map_cong)
         apply fastforce
        apply fastforce
       apply fastforce
    apply (metis domIff extends_subst_def option.simps(3))
    apply (metis domIff extends_subst_def option.simps(3))
    apply (metis domIff extends_subst_def option.inject option.simps(3))
  apply (drule meta_spec2)
  apply (drule meta_mp)
   apply (rule refl)
  apply (drule meta_mp)
   apply assumption
   apply (fastforce simp: list_eq_iff_nth_eq Ball_def UN_subset_iff in_set_zip in_set_conv_nth)
  apply (drule meta_spec2)
  apply (drule meta_mp)
   apply (rule refl)
  apply (drule meta_mp)
   apply assumption
  apply (fastforce simp: list_eq_iff_nth_eq Ball_def in_set_zip in_set_conv_nth)
  done

lemma match_term_list_complete: "match_term_list tus \<sigma> = None \<Longrightarrow>
  (\<Union>(t, u)\<in>set tus. vars_term t) \<subseteq> dom \<tau> \<Longrightarrow> extends_subst \<sigma> \<tau> \<Longrightarrow>
    (\<exists>(t,u)\<in>set tus. t \<cdot> subst_of_map Var \<tau> \<noteq> u)"
  apply (induct tus \<sigma> arbitrary: \<tau> rule: match_term_list.induct)
     apply (auto simp: extends_subst_refl exteinds_subst_fun_upd_new exteinds_subst_fun_upd_matching
      subst_of_map_def split: if_splits option.splits
      cong: list.map_cong)
   apply (auto simp: extends_subst_def dom_def) []
  apply (drule meta_spec2)
  apply (drule meta_mp)
   apply (rule refl)
  apply (drule meta_mp)
   apply assumption
  apply (drule meta_mp)
   prefer 2
   apply (drule meta_mp)
    apply assumption
   apply (drule decompose_Some; auto)
   apply (fastforce simp: list_eq_iff_nth_eq Ball_def in_set_zip in_set_conv_nth)
  apply (drule decompose_Some; auto simp: dom_def Ball_def UN_subset_iff in_set_zip)
  apply (drule spec)
  apply (drule mp)
   prefer 2
   apply (drule set_mp, assumption)
   apply auto
  done
  

lemma subsumes_list_alt:
  "subsumes_list Ls Ks \<sigma> \<longleftrightarrow> subsumes_list_modulo Ls Ks \<sigma>"
proof (induction Ls Ks \<sigma> rule: subsumes_list.induct[case_names Nil Cons])
  case (Cons L Ls Ks \<sigma>)
  then show ?case
    apply (auto simp: subsumes_list_modulo_Cons subsumes_list.simps(2)[of L Ls Ks]
      find_None_iff find_Some_iff Let_def
      split: option.splits)
    sorry
qed (auto simp: subsumes_modulo_def subst_cls_def vars_clause_def intro: extends_subst_refl) 

lemma subsumes_subsumes_list[code_unfold]:
  "subsumes (mset Ls) (mset Ks) = subsumes_list Ls Ks Map.empty"
unfolding subsumes_list_alt[of Ls Ks Map.empty]
proof
  assume "subsumes (mset Ls) (mset Ks)"
  then obtain \<sigma> where "subst_cls (mset Ls) \<sigma> \<subseteq># mset Ks" unfolding subsumes_def by blast
  moreover define \<tau> where "\<tau> = Some o \<sigma>"
  ultimately show "subsumes_list_modulo Ls Ks Map.empty"
    unfolding subsumes_modulo_def
    by (auto intro!: exI[of _ \<tau>] simp: extends_subst_empty subst_of_map_def[abs_def])
qed (auto simp: subsumes_modulo_def extends_subst_empty subst_lit_def subsumes_def)

lemma strictly_subsumes_subsumes_list[code_unfold]:
  "strictly_subsumes (mset Ls) (mset Ks) = (subsumes_list Ls Ks Map.empty \<and> \<not> subsumes_list Ks Ls Map.empty)"
  unfolding strictly_subsumes_def subsumes_subsumes_list by simp

end
