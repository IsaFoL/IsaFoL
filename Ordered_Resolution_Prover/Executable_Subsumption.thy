(*  Title:       An Executable Algorithm for Clause Subsumption
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>An Executable Algorithm for Clause Subsumption\<close>

theory Executable_Subsumption
  imports IsaFoR_Term "$ISAFOR/Rewriting/Matching"
begin

fun subsumes_list where
  "subsumes_list [] Ks \<sigma> = True"
| "subsumes_list (L # Ls) Ks \<sigma> =
     (\<exists>K \<in> set Ks. is_pos K = is_pos L \<and>
       (case match_term_list [(atm_of L, atm_of K)] \<sigma> of
         None \<Rightarrow> False
       | Some \<rho> \<Rightarrow> subsumes_list Ls (remove1 K Ks) \<rho>))"

lemma atm_of_map_literal[simp]: "atm_of (map_literal f l) = f (atm_of l)"
  by (cases l; simp)

definition "extends_subst \<sigma> \<tau> = (\<forall>x \<in> dom \<sigma>. \<sigma> x = \<tau> x)"

lemma extends_subst_refl[simp]: "extends_subst \<sigma> \<sigma>"
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

lemma extends_subst_empty[simp]: "extends_subst Map.empty \<tau>"
  unfolding extends_subst_def by auto

lemma extends_subst_cong_term:
  "extends_subst \<sigma> \<tau> \<Longrightarrow> vars_term t \<subseteq> dom \<sigma> \<Longrightarrow> t \<cdot> subst_of_map Var \<sigma> = t \<cdot> subst_of_map Var \<tau>"
  by (force simp: extends_subst_def subst_of_map_def split: option.splits intro!: term_subst_eq)

lemma extends_subst_cong_lit:
  "extends_subst \<sigma> \<tau> \<Longrightarrow> vars_lit L \<subseteq> dom \<sigma> \<Longrightarrow> L \<cdot>lit subst_of_map Var \<sigma> = L \<cdot>lit subst_of_map Var \<tau>"
  by (cases L) (auto simp: extends_subst_cong_term)

definition "subsumes_modulo C D \<sigma> =
   (\<exists>\<tau>. dom \<tau> = vars_clause C \<union> dom \<sigma> \<and> extends_subst \<sigma> \<tau> \<and> subst_cls C (subst_of_map Var \<tau>) \<subseteq># D)"

abbreviation subsumes_list_modulo where
  "subsumes_list_modulo Ls Ks \<sigma> \<equiv> subsumes_modulo (mset Ls) (mset Ks) \<sigma>"

lemma vars_clause_add_mset[simp]: "vars_clause (add_mset L C) = vars_lit L \<union> vars_clause C"
  unfolding vars_clause_def by auto

lemma subsumes_list_modulo_Cons: "subsumes_list_modulo (L # Ls) Ks \<sigma> \<longleftrightarrow>
  (\<exists>K \<in> set Ks. \<exists>\<tau>. extends_subst \<sigma> \<tau> \<and> dom \<tau> = vars_lit L \<union> dom \<sigma> \<and> L \<cdot>lit (subst_of_map Var \<tau>) = K
     \<and> subsumes_list_modulo Ls (remove1 K Ks) \<tau>)"
  unfolding subsumes_modulo_def
  apply safe
   apply (auto simp: insert_subset_eq_iff subst_lit_def subst_cls_def literal.map_ident
     intro: extends_subst_refl extends_subst_trans)
   apply (erule bexI[rotated])
  subgoal for \<tau>
    apply (rule exI[of _ "\<lambda>x. if x \<in> vars_lit L \<union> dom \<sigma> then \<tau> x else None"], intro conjI)
         apply (auto 0 3 simp: extends_subst_def dom_def split: if_splits
        intro!: extends_subst_cong_lit exI[of _ \<tau>])
    done
  subgoal for \<tau> \<tau>'
    apply (rule exI[of _ \<tau>'])
    apply (auto simp: extends_subst_cong_lit elim!: extends_subst_trans)
    done
  done

lemma match_term_list_sound: "match_term_list tus \<sigma> = Some \<tau> \<Longrightarrow>
  extends_subst \<sigma> \<tau> \<and> dom \<tau> = (\<Union>(t, u)\<in>set tus. vars_term t) \<union> dom \<sigma> \<and>
  (\<forall>(t,u)\<in>set tus. t \<cdot> subst_of_map Var \<tau> = u)"
  apply (induct tus \<sigma> arbitrary: \<tau> rule: match_term_list.induct)
     apply (auto simp: exteinds_subst_fun_upd_new exteinds_subst_fun_upd_matching
      subst_of_map_def split: if_splits option.splits
      cong: list.map_cong)
      apply fastforce
     apply (metis domI extends_subst_def option.inject)
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
  apply (drule meta_spec2)
  apply (drule meta_mp)
  apply (rule refl)
  apply (drule meta_mp)
  apply assumption
  apply (fastforce simp: list_eq_iff_nth_eq Ball_def in_set_zip in_set_conv_nth)
  done

lemma match_term_list_complete: "match_term_list tus \<sigma> = None \<Longrightarrow>
   extends_subst \<sigma> \<tau> \<Longrightarrow> dom \<tau> = (\<Union>(t, u)\<in>set tus. vars_term t) \<union> dom \<sigma> \<Longrightarrow>
    (\<exists>(t,u)\<in>set tus. t \<cdot> subst_of_map Var \<tau> \<noteq> u)"
  apply (induct tus \<sigma> arbitrary: \<tau> rule: match_term_list.induct)
     apply (auto simp: exteinds_subst_fun_upd_new exteinds_subst_fun_upd_matching
      subst_of_map_def split: if_splits option.splits
      cong: list.map_cong)
   apply (auto simp: extends_subst_def dom_def) []
  apply (drule meta_spec2)
  apply (drule meta_mp)
   apply (rule refl)
  apply (drule meta_mp)
   apply assumption
  apply (drule meta_mp)
    apply assumption
  apply (drule meta_mp)
   apply (drule decompose_Some; auto simp: dom_def Ball_def UN_subset_iff in_set_zip)
   apply (drule spec)
   apply (drule mp)
    prefer 2
    apply auto [2]
   apply (fastforce simp: list_eq_iff_nth_eq Ball_def in_set_zip in_set_conv_nth)
  apply (drule decompose_Some; auto)
  apply (fastforce simp: list_eq_iff_nth_eq Ball_def in_set_zip in_set_conv_nth)
  done

lemma unique_extends_subst:
  assumes extends: "extends_subst \<sigma> \<tau>" "extends_subst \<sigma> \<rho>"
      and dom: "dom \<tau> = vars_term t \<union> dom \<sigma>" "dom \<rho> = vars_term t \<union> dom \<sigma>"
      and eq: "t \<cdot> subst_of_map Var \<rho> = t \<cdot> subst_of_map Var \<tau>"
  shows "\<rho> = \<tau>"
proof
  fix x
  consider (a) "x \<in> dom \<sigma>" | (b) "x \<in> vars_term t" | (c) "x \<notin> dom \<tau>" using assms by auto
  then show "\<rho> x = \<tau> x"
  proof cases
    case a
    then show ?thesis using extends unfolding extends_subst_def by auto
  next
    case b
    with eq show ?thesis
    proof (induct t)
      case (Var x)
      with trans[OF dom(1) dom(2)[symmetric]] show ?case
        by (auto simp: subst_of_map_def split: option.splits)
    qed auto
  next
    case c
    then have "\<rho> x = None" "\<tau> x = None" using dom by auto
    then show ?thesis by simp
  qed
qed

lemma subsumes_list_alt:
  "subsumes_list Ls Ks \<sigma> \<longleftrightarrow> subsumes_list_modulo Ls Ks \<sigma>"
proof (induction Ls Ks \<sigma> rule: subsumes_list.induct[case_names Nil Cons])
  case (Cons L Ls Ks \<sigma>)
  show ?case
    unfolding subsumes_list_modulo_Cons subsumes_list.simps
    apply (auto simp: Cons.IH split: option.splits elim!: bexI[rotated] dest!: match_term_list_sound)
    subgoal for K \<tau>
      apply (cases "match_term_list [(atm_of L, atm_of K)] \<sigma>")
      subgoal by (auto dest!: match_term_list_complete)
      subgoal for \<tau>' by (cases K; cases L; auto dest!: match_term_list_sound)
      done
    subgoal for \<tau>
      using match_term_list_complete[of "[(atm_of L, atm_of L \<cdot> subst_of_map Var \<tau>)]" \<sigma> \<tau>]
      by auto
    subgoal for \<tau> \<rho>
      using unique_extends_subst[of \<sigma> \<tau> \<rho> "atm_of L"]
      by auto
    done
qed (auto simp: subsumes_modulo_def subst_cls_def vars_clause_def intro: extends_subst_refl) 

lemma subsumes_subsumes_list[code_unfold]:
  "subsumes (mset Ls) (mset Ks) = subsumes_list Ls Ks Map.empty"
unfolding subsumes_list_alt[of Ls Ks Map.empty]
proof
  assume "subsumes (mset Ls) (mset Ks)"
  then obtain \<sigma> where "subst_cls (mset Ls) \<sigma> \<subseteq># mset Ks" unfolding subsumes_def by blast
  moreover define \<tau> where "\<tau> = (\<lambda>x. if x \<in> vars_clause (mset Ls) then Some (\<sigma> x) else None)"
  ultimately show "subsumes_list_modulo Ls Ks Map.empty"
    unfolding subsumes_modulo_def
    by (subst (asm) same_on_vars_clause[of _ \<sigma> "subst_of_map Var \<tau>"])
      (auto intro!: exI[of _ \<tau>] simp: subst_of_map_def[abs_def] split: if_splits)
qed (auto simp: subsumes_modulo_def subst_lit_def subsumes_def)

lemma strictly_subsumes_subsumes_list[code_unfold]:
  "strictly_subsumes (mset Ls) (mset Ks) = (subsumes_list Ls Ks Map.empty \<and> \<not> subsumes_list Ks Ls Map.empty)"
  unfolding strictly_subsumes_def subsumes_subsumes_list by simp

end
