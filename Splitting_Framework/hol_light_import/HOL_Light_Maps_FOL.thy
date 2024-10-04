(*  Title:      HOL_Light_Maps_FOL.thy
    Author:     Stéphane Glondu, Inria, 2024
*)

section \<open>Type and constant mappings of HOL Light's FOL theory\<close>

theory HOL_Light_Maps_FOL
  imports
    Import_Setup
    First_Order_Terms.Term
    FOL_Syntax
begin

type_synonym nterm = \<open>(nat, nat) term\<close>
import_type_map "term" : nterm
import_const_map V : Var
import_const_map Fn : Fun

lemma term_INDUCT: "\<forall>(P :: nterm \<Rightarrow> bool). (\<forall>v. P (Var v)) \<and> (\<forall>s l. list_all P l \<longrightarrow> P (Fun s l)) \<longrightarrow> (\<forall>t. P t)"
proof
  fix P :: "nterm \<Rightarrow> bool"
  show "(\<forall>v. P (Var v)) \<and> (\<forall>s l. list_all P l \<longrightarrow> P (Fun s l)) \<longrightarrow> (\<forall>t. P t)"
  proof
    assume "(\<forall>v. P (Var v)) \<and> (\<forall>s l. list_all P l \<longrightarrow> P (Fun s l))"
    hence "(\<forall>v. P (Var v)) \<and> (\<forall>s l. (\<forall>x. x \<in> set l \<longrightarrow> P x) \<longrightarrow> P (Fun s l))"
      by (simp add: list.pred_set)
    thus "\<forall>t. P t"
      using term.induct by blast
  qed
qed

primrec build_term_function :: "(nat \<Rightarrow> 'Z) \<Rightarrow> (nat \<Rightarrow> nterm list \<Rightarrow> 'Z list \<Rightarrow> 'Z) \<Rightarrow> nterm \<Rightarrow> 'Z" where
  "build_term_function f h (Var v) = f v"
| "build_term_function f h (Fun s l) = h s l (map (build_term_function f h) l)"

lemma term_RECURSION: "\<forall>(f :: nat \<Rightarrow> 'Z) (h :: nat \<Rightarrow> nterm list \<Rightarrow> 'Z list \<Rightarrow> 'Z). \<exists>fn. (\<forall>v. fn (Var v) = f v) \<and> (\<forall>s l. fn (Fun s l :: nterm) = h s l (map fn l))"
proof clarsimp
  fix
    f :: "nat \<Rightarrow> 'Z" and
    h :: "nat \<Rightarrow> nterm list \<Rightarrow> 'Z list \<Rightarrow> 'Z"
  define fn where "fn = build_term_function f h"
  hence "(\<forall>v. fn (Var v) = f v) \<and> (\<forall>s l. fn (Fun s l :: nterm) = h s l (map fn l))"
    by simp
  thus "\<exists>fn. (\<forall>v. fn (Var v) = f v) \<and> (\<forall>s l. fn (Fun s l :: nterm) = h s l (map fn l))"
    by blast
qed

import_type_map form : form
import_const_map False : Bot
import_const_map Atom : Atom
import_const_map "-->" : Implies
import_const_map "!!" : Forall

lemma form_INDUCTION:
  "\<forall>P. P Bot \<and> (\<forall>a0 a1. P (Atom a0 a1)) \<and> (\<forall>a0 a1. P a0 \<and> P a1 \<longrightarrow> P (Implies a0 a1)) \<and> (\<forall>a0 a1. P a1 \<longrightarrow> P (Forall a0 a1)) \<longrightarrow> (\<forall>x. P x)"
proof
  fix P :: "form \<Rightarrow> bool"
  show "P \<^bold>\<bottom> \<and> (\<forall>a0 a1. P (Atom a0 a1)) \<and> (\<forall>a0 a1. P a0 \<and> P a1 \<longrightarrow> P (a0 \<^bold>\<longrightarrow> a1)) \<and> (\<forall>a0 a1. P a1 \<longrightarrow> P (\<^bold>\<forall> a0\<^bold>. a1)) \<longrightarrow> (\<forall>x. P x)"
  proof
    assume "P \<^bold>\<bottom> \<and> (\<forall>a0 a1. P (Atom a0 a1)) \<and> (\<forall>a0 a1. P a0 \<and> P a1 \<longrightarrow> P (a0 \<^bold>\<longrightarrow> a1)) \<and> (\<forall>a0 a1. P a1 \<longrightarrow> P (\<^bold>\<forall> a0\<^bold>. a1))"
    thus "\<forall>x. P x"
      using form.induct by blast
  qed
qed

primrec build_form_function :: "'Z \<Rightarrow> (nat \<Rightarrow> nterm list \<Rightarrow> 'Z) \<Rightarrow> (form \<Rightarrow> form \<Rightarrow> 'Z \<Rightarrow> 'Z \<Rightarrow> 'Z) \<Rightarrow> (nat \<Rightarrow> form \<Rightarrow> 'Z \<Rightarrow> 'Z) \<Rightarrow> form \<Rightarrow> 'Z" where
  "build_form_function f0 f1 f2 f3 Bot = f0"
| "build_form_function f0 f1 f2 f3 (Atom n a) = f1 n a"
| "build_form_function f0 f1 f2 f3 (Implies a b) = f2 a b (build_form_function f0 f1 f2 f3 a) (build_form_function f0 f1 f2 f3 b)"
| "build_form_function f0 f1 f2 f3 (Forall n a) = f3 n a (build_form_function f0 f1 f2 f3 a)"

lemma form_RECURSION:
  "\<forall>(f0 :: 'Z) f1 f2 f3. \<exists>fn. fn Bot = f0 \<and> (\<forall>a0 a1. fn (Atom a0 a1) = f1 a0 a1) \<and> (\<forall>a0 a1. fn (Implies a0 a1) = f2 a0 a1 (fn a0) (fn a1)) \<and> (\<forall>a0 a1. fn (Forall a0 a1) = f3 a0 a1 (fn a1))"
proof clarsimp
  fix
    f0 :: "'Z" and
    f1 :: "nat \<Rightarrow> nterm list \<Rightarrow> 'Z" and
    f2 :: "form \<Rightarrow> form \<Rightarrow> 'Z \<Rightarrow> 'Z \<Rightarrow> 'Z" and
    f3 :: "nat \<Rightarrow> form \<Rightarrow> 'Z \<Rightarrow> 'Z"
  define fn where "fn = build_form_function f0 f1 f2 f3"
  hence "fn Bot = f0 \<and> (\<forall>a0 a1. fn (Atom a0 a1) = f1 a0 a1) \<and> (\<forall>a0 a1. fn (Implies a0 a1) = f2 a0 a1 (fn a0) (fn a1)) \<and> (\<forall>a0 a1. fn (Forall a0 a1) = f3 a0 a1 (fn a1))"
    by simp
  thus "\<exists>fn. fn Bot = f0 \<and> (\<forall>a0 a1. fn (Atom a0 a1) = f1 a0 a1) \<and> (\<forall>a0 a1. fn (Implies a0 a1) = f2 a0 a1 (fn a0) (fn a1)) \<and> (\<forall>a0 a1. fn (Forall a0 a1) = f3 a0 a1 (fn a1))"
    by blast
qed

end
