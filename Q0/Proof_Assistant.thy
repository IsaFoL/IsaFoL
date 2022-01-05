theory Proof_Assistant imports Q0 begin

(* Experiment:
   Can we make a proof assistant in the style of FOL_Harrison/SPA?
   (not in the book) *)

typedef wff = "{Some t|t. \<exists>\<alpha>. wff \<alpha> t} \<union> {None}"
  using wff_Con_Aux1 by blast

typedef "thm" = "{Some A|A. theorem A} \<union> {None}"
  using theorem.intros axiom.intros by auto

setup_lifting type_definition_wff
setup_lifting type_definition_thm

definition mk_wff_aux :: "type_sym \<Rightarrow> form \<Rightarrow> form option" where
  "mk_wff_aux \<alpha> A = (if wff \<alpha> A then Some A else None)"

lift_definition mk_wff :: "type_sym \<Rightarrow> form \<Rightarrow> wff" is mk_wff_aux
  unfolding mk_wff_aux_def by auto

lift_definition axiom_1_thm :: "thm" is "Some axiom_1"
  using theorem.intros axiom.intros by auto

lift_definition axiom_2_thm :: "type_sym \<Rightarrow> thm" is "\<lambda>\<alpha>. Some (axiom_2 \<alpha>)"
  using theorem.intros axiom.intros by auto

lift_definition axiom_3_thm :: "type_sym \<Rightarrow> type_sym \<Rightarrow> thm" is "\<lambda>\<alpha> \<beta>. Some (axiom_3 \<alpha> \<beta>)"
  using theorem.intros axiom.intros by auto

definition axiom_4_1_thm_aux :: "var_sym \<Rightarrow> type_sym \<Rightarrow> form option \<Rightarrow> type_sym \<Rightarrow> form option \<Rightarrow> form option" where
  "axiom_4_1_thm_aux x \<alpha> B \<beta> A = (if wff \<alpha> (the A) \<and> wff \<beta> (the B) \<and> axiom_4_1_side_condition x \<alpha> (the B) \<beta> (the A) then Some (axiom_4_1 x \<alpha> (the B) \<beta> (the A)) else None)"

lemma[code]: 
  "axiom_4_1_side_condition x \<alpha> B \<beta> A = (case B of Cst s \<beta>' \<Rightarrow> \<beta> = \<beta>' | Var s \<beta>' \<Rightarrow> \<beta> = \<beta>' \<and> x \<noteq> s | _ \<Rightarrow> False)"
  unfolding axiom_4_1_side_condition_def
  apply (cases B)
     apply auto
  done

lift_definition axiom_4_1_thm :: "var_sym \<Rightarrow> type_sym \<Rightarrow> wff \<Rightarrow> type_sym \<Rightarrow> wff \<Rightarrow> thm" is axiom_4_1_thm_aux
  unfolding axiom_4_1_thm_aux_def
  subgoal for list type_sym1 form1 type_sym2 form2
    apply (cases "axiom_4_1_side_condition list type_sym1 (the form1) type_sym2 (the form2)")
    subgoal
      using theorem.intros axiom.intros
      apply auto
      done
    subgoal
      apply auto
      done
    done
  done

fun replacements :: "form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> form list" where
  "replacements A B (Var x \<alpha>) =
     (if A = (Var x \<alpha>) then [B] else [])"
| "replacements A B (Cst c \<alpha>) =
     (if A = (Cst c \<alpha>) then [B] else [])"
| "replacements A B (App C D) =
     (if A = (App C D) then [B] else []) @
     map (\<lambda>E. App E D) (replacements A B C) @
     map (\<lambda>E. App C E) (replacements A B D)"
| "replacements A B (Abs x \<alpha> C) =
     (if A = (Abs x \<alpha> C) then [B] else []) @
     map (\<lambda>D. Abs x \<alpha> D) (replacements A B C)"

lemma replacement_if_in_replacements:
  assumes "D \<in> set (replacements A B C)"
  shows "replacement A B C D"
  using assms using replacement.intros by (induction C arbitrary: D) auto

(*   "replacement A B C D \<Longrightarrow> rule_R C (Eql A B \<alpha>) D" *)


abbreviation Eql_pattern :: "form \<Rightarrow> form \<Rightarrow> type_sym \<Rightarrow> type_sym \<Rightarrow> form" where
  "Eql_pattern A B \<alpha>1 \<alpha>2 \<equiv> App (App (Cst ''Q'' (Fun (Fun Tv \<alpha>1) \<alpha>2)) A) B"

definition is_Eql :: "form \<Rightarrow> bool" where
  "is_Eql EqlAB = (case EqlAB of
     Eql_pattern A B \<alpha>1 \<alpha>2 \<Rightarrow> card {\<alpha>1, \<alpha>2} = 1
   | _ \<Rightarrow> False)"

lemma Eql_if_is_Eql: "is_Eql EqlAB \<Longrightarrow> (\<exists>A B \<alpha>. EqlAB = Eql A B \<alpha>)"
  unfolding is_Eql_def
  apply (auto split: form.splits)
  subgoal for x32 x32a x21 x22
    apply (cases "x21 = ''Q''")
     apply auto
    subgoal
      apply (auto split: type_sym.splits)
      subgoal for \<alpha>2 \<alpha>1
        unfolding Eql_def
        apply auto
             apply (smt card_Suc_eq insertI1 insert_commute singletonD)+
        done
      done
    subgoal
      apply (subgoal_tac "False")
      subgoal
        apply auto
        done
      subgoal
        apply (auto split: list.splits)
        subgoal for x21a
          apply (cases x21a)
          apply (auto split: list.splits)
                apply smt+
          done
        subgoal for x21a
          apply (cases x21a)
          apply (auto split: list.splits)
          apply smt+
          done
        done
      done
    done
  done

definition is_Some_Eql :: "form option \<Rightarrow> bool" where
  "is_Some_Eql SomeEqlAB = (case SomeEqlAB of 
     Some EqlAB \<Rightarrow> is_Eql EqlAB
   | _ \<Rightarrow> False)"

definition Eql_LHS :: "form \<Rightarrow> form" where
  "Eql_LHS EqlAB = (case EqlAB of 
     Eql_pattern A B \<alpha>1 \<alpha>2 \<Rightarrow> A
   | _ \<Rightarrow> undefined)"

lemma[simp]: "Eql_LHS (Eql A B \<alpha>) = A"
  apply code_simp done

definition Eql_RHS :: "form \<Rightarrow> form" where
  "Eql_RHS EqlAB = (case EqlAB of 
     Eql_pattern A B \<alpha>1 \<alpha>2 \<Rightarrow> B
   | _ \<Rightarrow> undefined)"

lemma[simp]: "Eql_RHS (Eql A B \<alpha>) = B"
  apply code_simp done

definition rule_R_aux :: "form option \<Rightarrow> form option \<Rightarrow> nat \<Rightarrow> form option" where
  "rule_R_aux C EqlAB n = 
    (let A = Eql_LHS (the EqlAB) in
    (let B = Eql_RHS (the EqlAB) in
    (let Ds = replacements A B (the C) in
       (if is_Some_Eql EqlAB \<and> C \<noteq> None \<and> n < length Ds 
        then Some (Ds ! n)        
        else None))))"

lift_definition rule_R_thm :: "thm \<Rightarrow> thm \<Rightarrow> nat \<Rightarrow> thm" is rule_R_aux
  subgoal for SomeC SomeEqlAB n
  proof -
    assume a:
      "SomeC \<in> {Some A |A. theorem A} \<union> {None}"
      "SomeEqlAB \<in> {Some A |A. theorem A} \<union> {None}"
    show "rule_R_aux SomeC SomeEqlAB n \<in> {Some A |A. theorem A} \<union> {None}"
    proof (cases SomeC; cases SomeEqlAB)
      assume 
        "SomeC = None" and
        "SomeEqlAB = None"
      then show "rule_R_aux SomeC SomeEqlAB n \<in> {Some A |A. theorem A} \<union> {None}"
        using a unfolding rule_R_aux_def is_Some_Eql_def by auto 
    next
      fix EqlAB :: "form"
      assume 
        "SomeC = None" and
        "SomeEqlAB = Some EqlAB"
      then show "rule_R_aux SomeC SomeEqlAB n \<in> {Some A |A. theorem A} \<union> {None}" 
        using a unfolding rule_R_aux_def is_Some_Eql_def by auto
    next
      fix C :: "form"
      assume 
        "SomeC = Some C" and
        "SomeEqlAB = None"
      then show "rule_R_aux SomeC SomeEqlAB n \<in> {Some A |A. theorem A} \<union> {None}" 
        using a unfolding rule_R_aux_def is_Some_Eql_def by auto
    next
      fix C :: "form" and EqlAB :: "form"
      assume b:
        "SomeC = Some C"
        "SomeEqlAB = Some EqlAB"
      let ?A = "Eql_LHS (the SomeEqlAB)" 
      let ?B = "Eql_RHS (the SomeEqlAB)"
      let ?Ds = "replacements ?A ?B (the SomeC)"
      show "rule_R_aux SomeC SomeEqlAB n \<in> {Some A |A. theorem A} \<union> {None}" 
      proof (cases "is_Some_Eql SomeEqlAB \<and> n < length ?Ds")
        case True
        then have "rule_R_aux SomeC SomeEqlAB n \<in> {Some A |A. theorem A}"
          unfolding rule_R_aux_def
          apply auto
          subgoal for C
            apply (rule theorem.intros(2)[of "C" "EqlAB"])
            subgoal
              using b a
              apply auto
              done
            subgoal
              using b a
              apply auto
              done
            subgoal
              unfolding is_Some_Eql_def
              using b
              apply auto
              using Eql_if_is_Eql[of EqlAB]
              apply auto
              subgoal for A B \<alpha>
                apply (rule rule_R.intros[of _ _ _])
                using replacement_if_in_replacements apply auto
                done
              done
            done
          using b apply auto
          done
        then show ?thesis 
          by auto
      next
        case False
        then have "rule_R_aux SomeC SomeEqlAB n \<in> {None}"
          unfolding rule_R_aux_def by auto
        then show ?thesis 
          by auto
      qed
    qed
  qed
  done

definition "concl \<equiv> the \<circ> Rep_thm"
definition "get_form \<equiv> the \<circ> Rep_wff"
declare concl_def[simp]
declare get_form_def[simp]

code_reflect
  Proven
  datatypes
    type_sym = Ind | Tv | Fun
    and
    form = Var | Cst | App | Abs
  functions
    Suc 0
    mk_wff axiom_1_thm axiom_2_thm axiom_4_1_thm rule_R_thm concl

ML \<open>
open Proven

fun rule_R_thm_all_aux C EqlAB n =
   (rule_R_thm C EqlAB n) :: (rule_R_thm_all_aux C EqlAB (Suc n))
   handle _ => []

fun rule_R_thm_all C EqlAB = rule_R_thm_all_aux C EqlAB Zero_nat
 \<close>

end