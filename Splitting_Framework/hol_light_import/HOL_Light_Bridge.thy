(*  Title:      HOL_Light_Bridge.thy
    Author:     Stéphane Glondu, Inria, 2024
*)

section \<open>HOL Light post-import bridge\<close>

theory HOL_Light_Bridge
  imports HOL_Light_Import FOL_Semantics
begin

definition list_union where "list_union = (\<lambda>L z. z \<in> (\<Union> A \<in> set L. Collect A))"

lemma LIST_UNION_equiv: "LIST_UNION t = list_union t"
proof (induction t)
  case Nil
  then show ?case
    by (simp add: LIST_UNION list_union_def empty_def)
next
  case (Cons a t)
  then show ?case
    by (simp add: LIST_UNION list_union_def union_def)
qed

definition unions where "unions = (\<lambda>s z. z \<in> (\<Union> A \<in> Collect s. Collect A))"

lemma UNIONS_equiv: "UNIONS s = unions s"
  by (simp add: UNIONS_hldef gspec_def setspec_def unions_def member_def)

lemma functions_term_equiv:
  "HOL_Light_Import.functions_term t = (\<lambda>z. z \<in> FOL_Syntax.functions_term t)"
proof (induction t)
  case (Var x)
  then show ?case
    by (simp add: functions_term empty_def functions_term.induct)
next
  case (Fun f ts)
  then show ?case
    by (simp add: functions_term LIST_UNION_equiv insert_def list_union_def)
qed

lemma functions_form_equiv:
  "HOL_Light_Import.functions_form f = (\<lambda>z. z \<in> FOL_Syntax.functions_form f)"
proof (induction f)
  case Bot
  then show ?case
    by (simp add: functions_form empty_def)
next
  case (Atom pred args)
  then show ?case
    by (simp add: functions_form LIST_UNION_equiv list_union_def functions_term_equiv)
next
  case (Implies f1 f2)
  then show ?case
    by (simp add: functions_form union_def)
next
  case (Forall x f)
  then show ?case
    by (simp add: functions_form)
qed

lemma functions_equiv:
  "HOL_Light_Import.functions fs = (\<lambda>z. z \<in> FOL_Syntax.functions_forms (Collect fs))"
  apply (simp add: HOL_Light_Import.functions UNIONS_equiv unions_def gspec_def setspec_def member_def functions_form_equiv functions_forms_def)
  by fastforce

lemma predicates_form_equiv:
  "HOL_Light_Import.predicates_form f = (\<lambda>z. z \<in> FOL_Syntax.predicates_form f)"
proof (induction f)
  case Bot
  then show ?case
    by (simp add: predicates_form empty_def)
next
  case (Atom pred args)
  then show ?case
    by (simp add: predicates_form insert_def empty_def)
next
  case (Implies f1 f2)
  then show ?case
    by (simp add: predicates_form union_def)
next
  case (Forall x f)
  then show ?case
    by (simp add: predicates_form)
qed

lemma predicates_equiv:
  "HOL_Light_Import.predicates fs = (\<lambda>z. z \<in> FOL_Syntax.predicates (Collect fs))"
  apply (simp add: HOL_Light_Import.predicates UNIONS_equiv unions_def gspec_def setspec_def member_def predicates_form_equiv predicates_def)
  by fastforce

type_synonym HOL_language = "(nat \<times> nat \<Rightarrow> bool) \<times> (nat \<times> nat \<Rightarrow> bool)"
type_synonym language = "(nat \<times> nat) set \<times> (nat \<times> nat) set"

definition language_to_HOL :: "language \<Rightarrow> HOL_language"
  where "language_to_HOL = (\<lambda>L. ((\<lambda>z. z \<in> fst L), (\<lambda>z. z \<in> snd L)))"

definition language_from_HOL :: "HOL_language \<Rightarrow> language"
  where "language_from_HOL = (\<lambda>L .(Collect (fst L), Collect (snd L)))"

lemma language_equiv:
  "HOL_Light_Import.language s = language_to_HOL (FOL_Syntax.language (Collect s))"
  by (simp add: HOL_Light_Import.language language_def language_to_HOL_def functions_equiv predicates_equiv)

type_synonym 'a HOL_intrp = "('a \<Rightarrow> bool) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> bool)"

definition intrp_to_HOL :: "'a intrp \<Rightarrow> 'a HOL_intrp"
  where "intrp_to_HOL = (\<lambda>C. ((\<lambda>z. z \<in> dom C), intrp_fn C, (\<lambda>n z. z \<in> intrp_rel C n)))"

definition intrp_from_HOL :: "'a HOL_intrp \<Rightarrow> 'a intrp"
  where "intrp_from_HOL = (\<lambda>C. Abs_intrp (Collect (fst C), fst (snd C), \<lambda>n. Collect (snd (snd C) n)))"

lemma list_all_equiv: "list.list_all P l = list_all P l"
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case by (simp add: fold_bool_prop)
qed

lemma interpretation_equiv:
  "is_interpretation L C = HOL_Light_Import.interpretation (language_to_HOL L) (intrp_to_HOL C)"
  apply (simp add: is_interpretation_def interpretation_hldef Fun_hldef intrp_fn_def Dom_hldef list_all_equiv member_def)
  by (simp add: intrp_fn.rep_eq intrp_to_HOL_def language_to_HOL_def)

lemma termval_equiv: "eval t C x = termval (intrp_to_HOL C) x t"
proof (induction t)
  case (Var x)
  then show ?case
    by (simp add: termval)
next
  case (Fun f ts)
  then show ?case
    apply (simp add: termval intrp_fn_def Fun_hldef)
    by (metis (mono_tags, lifting) fst_eqD intrp_fn.rep_eq intrp_to_HOL_def map_eq_conv snd_eqD)
qed

lemma holds_equiv: "\<forall>x. FOL_Semantics.holds C x f = HOL_Light_Import.holds (intrp_to_HOL C) x f"
proof (induction f)
  case Bot
  then show ?case by (simp add: holds)
next
  case (Atom pred args)
  then show ?case
    by (simp add: holds intrp_rel_def termval_equiv Pred_hldef intrp_rel.rep_eq intrp_to_HOL_def)
next
  case (Implies f1 f2)
  then show ?case
    by (simp add: holds)
next
  case (Forall x1 f)
  then show ?case
    apply (simp add: holds Dom_hldef intrp_rel.rep_eq intrp_to_HOL_def member_def valmod_hldef)
    by (metis (no_types) snd_conv)
qed

lemma satisfies_equiv:
  "FOL_Semantics.satisfies C fs = HOL_Light_Import.satisfies (intrp_to_HOL C) (\<lambda>z. z \<in> fs)"
  by (simp add: is_valuation_def satisfies_def satisfies_hldef holds_equiv member_def 
      valuation_hldef Dom_hldef intrp_to_HOL_def)

lemma COMPACT_LS:
  "(\<forall>t. Finite_Set.finite t \<and> t \<subseteq> s \<longrightarrow> (\<exists>M. is_interpretation (FOL_Syntax.language s) M \<and> satisfies M t)) \<longrightarrow>
   (\<exists>(C :: nterm intrp). is_interpretation (FOL_Syntax.language s) C \<and> satisfies C s)"
proof
  define S where "S = (\<lambda>z. z \<in> s)"
  assume finite_models: "\<forall>t. Finite_Set.finite t \<and> t \<subseteq> s \<longrightarrow> (\<exists>(M :: 'a intrp). is_interpretation (FOL_Syntax.language s) M \<and> satisfies M t)"
  have "\<forall>t. finite t \<and> subset t S \<longrightarrow> (\<exists>(M :: 'a HOL_intrp). HOL_Light_Import.interpretation (HOL_Light_Import.language S) M \<and> HOL_Light_Import.Dom M \<noteq> empty \<and> HOL_Light_Import.satisfies M t)"
  proof
    fix t :: "form \<Rightarrow> bool"
    define T where "T = Collect t"
    show "finite t \<and> subset t S \<longrightarrow> (\<exists>(M :: 'a HOL_intrp). HOL_Light_Import.interpretation (HOL_Light_Import.language S) M \<and> HOL_Light_Import.Dom M \<noteq> empty \<and> HOL_Light_Import.satisfies M t)"
    proof
      assume "finite t \<and> subset t S"
      hence "Finite_Set.finite T \<and> T \<subseteq> s"
        unfolding T_def finite_def subset_def S_def by blast
      hence "\<exists>(M :: 'a intrp). is_interpretation (FOL_Syntax.language s) M \<and> satisfies M T"
        using finite_models by blast
      then obtain M :: "'a intrp" where M_def: "is_interpretation (FOL_Syntax.language s) M \<and> satisfies M T"
        by blast
      define C where "C = intrp_to_HOL M"
      have "HOL_Light_Import.interpretation (HOL_Light_Import.language S) C"
        using M_def interpretation_equiv C_def S_def
        by (metis Collect_mem_eq language_equiv)
      moreover have "HOL_Light_Import.Dom C \<noteq> empty"
        apply (simp add: Dom_hldef C_def intrp_to_HOL_def)
        by (metis HOL_Light_Maps_Set.empty_def intrp_is_struct some_in_eq struct_def)
      moreover have "HOL_Light_Import.satisfies C t"
        using M_def satisfies_equiv C_def T_def by force
      ultimately have "HOL_Light_Import.interpretation (HOL_Light_Import.language S) C \<and> HOL_Light_Import.Dom C \<noteq> empty \<and> HOL_Light_Import.satisfies C t"
        by blast
      thus "\<exists>(M :: 'a HOL_intrp). HOL_Light_Import.interpretation (HOL_Light_Import.language S) M \<and> HOL_Light_Import.Dom M \<noteq> empty \<and> HOL_Light_Import.satisfies M t"
        by blast
    qed
  qed
  hence "\<exists>(C :: nterm HOL_intrp). HOL_Light_Import.interpretation (HOL_Light_Import.language S) C \<and> HOL_Light_Import.Dom C \<noteq> empty \<and> HOL_Light_Import.satisfies C S"
    using HOL_Light_Import.COMPACT_LS by blast
  then obtain C :: "nterm HOL_intrp"
    where C_def: "HOL_Light_Import.interpretation (HOL_Light_Import.language S) C \<and> HOL_Light_Import.Dom C \<noteq> empty \<and> HOL_Light_Import.satisfies C S"
    by blast
  define C' where "C' = intrp_from_HOL C"
  have C_def': "C = intrp_to_HOL C'"
  proof (cases C)
    case (fields M FN REL)
    have "struct (Collect M)"
    proof
      show "Collect M \<noteq> {}"
      proof -
        have "(HOL_Light_Maps_Set.empty::(nat, nat) Term.term \<Rightarrow> bool) = bot"
          by (simp add: HOL_Light_Maps_Set.empty_def bot_empty_eq)
        then show ?thesis
          by (metis C_def Collect_empty_eq_bot Dom_hldef fields fst_conv)
      qed
    qed
    hence "Rep_intrp (Abs_intrp (Collect (fst C), fst (snd C), \<lambda>n. Collect (snd (snd C) n))) = (Collect (fst C), fst (snd C), \<lambda>n. Collect (snd (snd C) n))"
      using intrp.Abs_intrp_inverse fields by auto
    then show ?thesis
      by (simp add: C'_def intrp_from_HOL_def intrp_to_HOL_def dom_def intrp_fn_def intrp_rel_def)
  qed
  have "is_interpretation (FOL_Syntax.language s) C' \<and> satisfies C' s"
    apply (simp add: interpretation_equiv satisfies_equiv C_def'[THEN HOL.sym])
    using C_def S_def language_equiv by auto
  thus "\<exists>(C :: nterm intrp). is_interpretation (FOL_Syntax.language s) C \<and> satisfies C s"
    by blast
qed

end
