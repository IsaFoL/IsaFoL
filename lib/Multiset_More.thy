(*  Title:       More about Multisets
    Author:      Jasmin Blanchette <blanchette at in.tum.de>, 2014, 2015
    Author:      Dmitriy Traytel <traytel at in.tum.de>, 2014
    Author:      Mathias Fleury <mathias.fleury@ens-rennes.fr>, 2015
    Maintainer:  Jasmin Blanchette <blanchette at in.tum.de>
*)


theory Multiset_More
imports "~~/src/HOL/Library/Multiset_Order"
begin

section {* More about Multisets *}

text {*
Isabelle's theory of finite multisets is not as developed as other areas, such as lists and sets.
The present theory introduces some missing concepts and lemmas. Some of it is expected to move to
Isabelle's library.
*}

subsection {* Basic Setup *}

declare
  diff_single_trivial [simp]
  ball_set_mset_iff [simp]
  in_image_mset [iff]
  image_mset_cong [cong]
  image_mset.compositionality [simp]

abbreviation not_Melem where
  "not_Melem x A \<equiv> ~ (x \<in># A)" -- "non-membership"

notation
  not_Melem  ("op ~:#") and
  not_Melem  ("(_/ ~:# _)" [51, 51] 50)

notation (xsymbols)
  not_Melem  ("op \<notin>#") and
  not_Melem  ("(_/ \<notin># _)" [51, 51] 50)

notation (HTML output)
  not_Melem  ("op \<notin>#") and
  not_Melem  ("(_/ \<notin># _)" [51, 51] 50)

subsection {* Existence quantifiers in multisets*}
definition Ball_mset :: "'a multiset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Ball_mset A P \<longleftrightarrow> (\<forall>x. x \<in># A \<longrightarrow> P x)"   -- "bounded universal quantifiers on multisets"

definition Bex_mset :: "'a multiset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Bex_mset A P \<longleftrightarrow> (\<exists>x. x \<in># A \<and> P x)"   -- "bounded existential quantifiers on multisets"

syntax
  "_Ball_mset"       :: "pttrn => 'a multiset => bool => bool"      ("(3ALL _:#_./ _)" [0, 0, 10] 10)
  "_Bex_mset"        :: "pttrn => 'a multiset => bool => bool"      ("(3EX _:#_./ _)" [0, 0, 10] 10)
  "_Bex1_mset"       :: "pttrn => 'a multiset => bool => bool"      ("(3EX! _:#_./ _)" [0, 0, 10] 10)
  "_Bleast_mset"     :: "id => 'a multiset => bool => 'a"           ("(3LEAST _:#_./ _)" [0, 0, 10] 10)

syntax (HOL)
  "_Ball_mset"       :: "pttrn => 'a multiset => bool => bool"      ("(3! _:#_./ _)" [0, 0, 10] 10)
  "_Bex_mset"        :: "pttrn => 'a multiset => bool => bool"      ("(3? _:#_./ _)" [0, 0, 10] 10)
  "_Bex1_mset"       :: "pttrn => 'a multiset => bool => bool"      ("(3?! _:#_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_Ball_mset"       :: "pttrn => 'a multiset => bool => bool"      ("(3\<forall>_\<in>#_./ _)" [0, 0, 10] 10)
  "_Bex_mset"        :: "pttrn => 'a multiset => bool => bool"      ("(3\<exists>_\<in>#_./ _)" [0, 0, 10] 10)
  "_Bex1_mset"       :: "pttrn => 'a multiset => bool => bool"      ("(3\<exists>!_\<in>#_./ _)" [0, 0, 10] 10)
  "_Bleast_mset"     :: "id => 'a multiset => bool => 'a"           ("(3LEAST_\<in>#_./ _)" [0, 0, 10] 10)

syntax (HTML output)
  "_Ball_mset"       :: "pttrn => 'a multiset => bool => bool"      ("(3\<forall>_\<in>#_./ _)" [0, 0, 10] 10)
  "_Bex_mset"        :: "pttrn => 'a multiset => bool => bool"      ("(3\<exists>_\<in>#_./ _)" [0, 0, 10] 10)
  "_Bex1_mset"       :: "pttrn => 'a multiset => bool => bool"      ("(3\<exists>!_\<in>#_./ _)" [0, 0, 10] 10)

translations
  "ALL x:#A. P" == "CONST Ball_mset A (%x. P)"
  "EX x:#A. P" == "CONST Bex_mset A (%x. P)"
  "EX! x:#A. P" => "EX! x. x:#A & P"
  "LEAST x:#A. P" => "LEAST x. x:#A & P"

(* Should probably be removed, once multiset is of sort ord again.*)
syntax (output)
  "_setlessAll" :: "[idt, 'a, bool] => bool"  ("(3ALL _<#_./ _)"  [0, 0, 10] 10)
  "_setlessEx"  :: "[idt, 'a, bool] => bool"  ("(3EX _<#_./ _)"  [0, 0, 10] 10)
  "_setleAll"   :: "[idt, 'a, bool] => bool"  ("(3ALL _<=#_./ _)" [0, 0, 10] 10)
  "_setleEx"    :: "[idt, 'a, bool] => bool"  ("(3EX _<=#_./ _)" [0, 0, 10] 10)
  "_setleEx1"   :: "[idt, 'a, bool] => bool"  ("(3EX! _<=#_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_setlessAll_mset" :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<subset>#_./ _)"  [0, 0, 10] 10)
  "_setlessEx_mset"  :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<subset>#_./ _)"  [0, 0, 10] 10)
  "_setleAll_mset"   :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<subseteq>#_./ _)" [0, 0, 10] 10)
  "_setleEx_mset"    :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<subseteq>#_./ _)" [0, 0, 10] 10)
  "_setleEx1_mset"   :: "[idt, 'a, bool] => bool"   ("(3\<exists>!_\<subseteq>#_./ _)" [0, 0, 10] 10)

syntax (HOL output)
  "_setlessAll_mset" :: "[idt, 'a, bool] => bool"   ("(3! _<#_./ _)"  [0, 0, 10] 10)
  "_setlessEx_mset"  :: "[idt, 'a, bool] => bool"   ("(3? _<#_./ _)"  [0, 0, 10] 10)
  "_setleAll_mset"   :: "[idt, 'a, bool] => bool"   ("(3! _<=#_./ _)" [0, 0, 10] 10)
  "_setleEx_mset"    :: "[idt, 'a, bool] => bool"   ("(3? _<=#_./ _)" [0, 0, 10] 10)
  "_setleEx1_mset"   :: "[idt, 'a, bool] => bool"   ("(3?! _<=#_./ _)" [0, 0, 10] 10)

syntax (HTML output)
  "_setlessAll_mset" :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<subset>#_./ _)"  [0, 0, 10] 10)
  "_setlessEx_mset"  :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<subset>#_./ _)"  [0, 0, 10] 10)
  "_setleAll_mset"   :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<subseteq>#_./ _)" [0, 0, 10] 10)
  "_setleEx_mset"    :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<subseteq>#_./ _)" [0, 0, 10] 10)
  "_setleEx1_mset"   :: "[idt, 'a, bool] => bool"   ("(3\<exists>!_\<subseteq>#_./ _)" [0, 0, 10] 10)

translations
 "\<forall>A\<subset>#B. P"   =>  "ALL A. A \<subset># B --> P"
 "\<exists>A\<subset>#B. P"   =>  "EX A. A \<subset># B & P"
 "\<forall>A\<subseteq>#B. P"   =>  "ALL A. A \<subseteq># B --> P"
 "\<exists>A\<subseteq>#B. P"   =>  "EX A. A \<subseteq># B & P"
 "\<exists>!A\<subseteq>#B. P"  =>  "EX! A. A \<subseteq># B & P"

print_translation {*
  let
    val All_mset_binder = Mixfix.binder_name @{const_syntax All};
    val Ex_mset_binder = Mixfix.binder_name @{const_syntax Ex};
    val impl = @{const_syntax HOL.implies};
    val conj = @{const_syntax HOL.conj};
    val sbset = @{const_syntax subset_mset};
    val sbset_eq = @{const_syntax subseteq_mset};

    val trans =
     [((All_mset_binder, impl, sbset), @{syntax_const "_setlessAll_mset"}),
      ((All_mset_binder, impl, sbset_eq), @{syntax_const "_setleAll_mset"}),
      ((Ex_mset_binder, conj, sbset), @{syntax_const "_setlessEx_mset"}),
      ((Ex_mset_binder, conj, sbset_eq), @{syntax_const "_setleEx_mset"})];

    fun mk v (v', T) c n P =
      if v = v' andalso not (Term.exists_subterm (fn Free (x, _) => x = v | _ => false) n)
      then Syntax.const c $ Syntax_Trans.mark_bound_body (v', T) $ n $ P
      else raise Match;

    fun tr' q = (q, fn _ =>
      (fn [Const (@{syntax_const "_bound"}, _) $ Free (v, Type (@{type_name multiset}, _)),
          Const (c, _) $
            (Const (d, _) $ (Const (@{syntax_const "_bound"}, _) $ Free (v', T)) $ n) $ P] =>
          (case AList.lookup (op =) trans (q, c, d) of
            NONE => raise Match
          | SOME l => mk v (v', T) l n P)
        | _ => raise Match));
  in
    [tr' All_mset_binder, tr' Ex_mset_binder]
  end
*}


print_translation {*
 [Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax Ball_mset} @{syntax_const "_Ball_mset"},
  Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax Bex_mset} @{syntax_const "_Bex_mset"}]
*} -- {* to avoid eta-contraction of body *}

simproc_setup defined_Bex_mset ("EX x:#A. P x & Q x") = {*
  fn _ => Quantifier1.rearrange_bex
    (fn ctxt =>
      unfold_tac ctxt @{thms Bex_mset_def} THEN
      Quantifier1.prove_one_point_ex_tac ctxt)
*}

simproc_setup defined_All_mset ("ALL x:#A. P x --> Q x") = {*
  fn _ => Quantifier1.rearrange_ball
    (fn ctxt =>
      unfold_tac ctxt @{thms Ball_mset_def} THEN
      Quantifier1.prove_one_point_all_tac ctxt)
*}

lemma ball_msetI [intro!]: "(!!x. x:#A ==> P x) ==> ALL x:#A. P x"
  by (simp add: Ball_mset_def)

lemma bspec_mset [dest?]: "ALL x:#A. P x ==> x:#A ==> P x"
  by (simp add: Ball_mset_def)

text {*
  Gives better instantiation for bound:
*}

(* TODO

What is it?*)
setup {*
  map_theory_claset (fn ctxt =>
    ctxt addbefore ("bspec_mset", fn ctxt' => dresolve_tac ctxt' @{thms bspec_mset} THEN' assume_tac ctxt'))
*}



ML {*
structure Simpdata =
struct

open Simpdata;

val mksimps_pairs_mset = [(@{const_name Ball_mset}, @{thms bspec_mset})] @ mksimps_pairs;

end;

open Simpdata;
*}

declaration {* fn _ =>
  Simplifier.map_ss (Simplifier.set_mksimps (mksimps mksimps_pairs_mset))
*}


lemma ball_msetE [elim]: "ALL x:#A. P x ==> (P x ==> Q) ==> (x ~:# A ==> Q) ==> Q"
  by (unfold Ball_mset_def) blast

lemma bex_msetI [intro]: "P x ==> x:#A ==> EX x:#A. P x"
  -- {* Normally the best argument order: @{prop "P x"} constrains the
    choice of @{prop "x:#A"}. *}
  by (unfold Bex_mset_def) blast

lemma rev_bex_msetI [intro]: "x:#A ==> P x ==> EX x:#A. P x"
  -- {* The best argument order when there is only one @{prop "x:#A"}. *}
  by (unfold Bex_mset_def) blast

lemma bex_msetCI: "(ALL x:#A. ~P x ==> P a) ==> a:#A ==> EX x:#A. P x"
  by (unfold Bex_mset_def) blast

lemma bexE [elim!]: "EX x:#A. P x ==> (!!x. x:#A ==> P x ==> Q) ==> Q"
  by (unfold Bex_mset_def) blast

lemma ball_mset_triv [simp]: "(ALL x:#A. P) = ((EX x. x:#A) --> P)"
  -- {* Trival rewrite rule. *}
  by (simp add: Ball_mset_def)

lemma bex_mset_triv [simp]: "(EX x:#A. P) = ((EX x. x:#A) & P)"
  -- {* Dual form for existentials. *}
  by (simp add: Bex_mset_def)

lemma bex_mset_triv_one_point1 [simp]: "(EX x:#A. x = a) = (a:#A)"
  by blast

lemma bex_mset_triv_one_point2 [simp]: "(EX x:#A. a = x) = (a:#A)"
  by blast

lemma bex_mset_one_point1 [simp]: "(EX x:#A. x = a & P x) = (a:#A & P a)"
  by blast

lemma bex_mset_one_point2 [simp]: "(EX x:#A. a = x & P x) = (a:#A & P a)"
  by blast

lemma ball_mset_one_point1 [simp]: "(ALL x:#A. x = a --> P x) = (a:#A --> P a)"
  by blast

lemma ball_mset_one_point2 [simp]: "(ALL x:#A. a = x --> P x) = (a:#A --> P a)"
  by blast

lemma ball_mset_conj_distrib:
  "(\<forall>x\<in>#A. P x \<and> Q x) \<longleftrightarrow> ((\<forall>x\<in>#A. P x) \<and> (\<forall>x\<in>#A. Q x))"
  by blast

lemma bex_disj_distrib:
  "(\<exists>x\<in>#A. P x \<or> Q x) \<longleftrightarrow> ((\<exists>x\<in>#A. P x) \<or> (\<exists>x\<in>#A. Q x))"
  by blast

text {* Congruence rules *}

lemma ball_mset_cong:
  "A = B ==> (!!x. x:#B ==> P x = Q x) ==>
    (ALL x:#A. P x) = (ALL x:#B. Q x)"
  by (simp add: Ball_mset_def)

lemma strong_ball_mset_cong [cong]:
  "A = B ==> (!!x. x:#B =simp=> P x = Q x) ==>
    (ALL x:#A. P x) = (ALL x:#B. Q x)"
  by (simp add: simp_implies_def Ball_mset_def)

lemma bex_cong:
  "A = B ==> (!!x. x:#B ==> P x = Q x) ==>
    (EX x:#A. P x) = (EX x:#B. Q x)"
  by (simp add: Bex_mset_def cong: conj_cong)

lemma strong_bex_cong [cong]:
  "A = B ==> (!!x. x:#B =simp=> P x = Q x) ==>
    (EX x:#A. P x) = (EX x:#B. Q x)"
  by (simp add: simp_implies_def Bex_mset_def cong: conj_cong)

lemma bex1_mset_def: "(\<exists>!x\<in>#X. P x) \<longleftrightarrow> (\<exists>x\<in>#X. P x) \<and> (\<forall>x\<in>#X. \<forall>y\<in>#X. P x \<longrightarrow> P y \<longrightarrow> x = y)"
  by auto

text {* More *}

text {*
  \medskip Eta-contracting these two rules (to remove @{text P})
  causes them to be ignored because of their interaction with
  congruence rules.
*}

subsection {* Lemmas about intersection*}
(* Unsure if suited as simp rules or if only slowing down stuff\<dots>*)
lemma mset_inter_single:
  "x \<in># \<Sigma> \<Longrightarrow> \<Sigma> #\<inter> {#x#} = {#x#}"
  "x \<notin># \<Sigma> \<Longrightarrow> \<Sigma> #\<inter> {#x#} = {#}"
    apply (simp add: mset_le_single subset_mset.inf_absorb2)
  by (simp add: multiset_inter_def)

subsection {* Lemmas about cardinality*}
text {*
This sections adds various lemmas about size. Most lemmas have a finite set equivalent.
*}
lemma size_Suc_Diff1:
  "x \<in># \<Sigma> \<Longrightarrow> Suc (size (\<Sigma> - {#x#})) = size \<Sigma>"
  using arg_cong[OF insert_DiffM, of _ _ size] by simp

lemma size_Diff_singleton: "x \<in># \<Sigma> \<Longrightarrow> size (\<Sigma> - {#x#}) = size \<Sigma> - 1"
  by (simp add: size_Suc_Diff1 [symmetric])

lemma size_Diff_singleton_if: "size (A - {#x#}) = (if x \<in># A then size A - 1 else size A)"
  by (simp add: size_Diff_singleton)

lemma size_Un_Int:
  "size A + size B = size (A #\<union> B) + size (A #\<inter> B)"
proof -
  have *: "A + B = B + (A - B + (A - (A - B)))"
    by (simp add: subset_mset.add_diff_inverse union_commute)
  have "size B + size (A - B) = size A + size (B - A)"
    unfolding size_union[symmetric] subset_mset.sup_commute sup_subset_mset_def[symmetric]
    by blast
  then show ?thesis unfolding multiset_inter_def size_union[symmetric] "*"
    by (auto simp add: sup_subset_mset_def)
qed

lemma size_Un_disjoint:
  assumes "A #\<inter> B = {#}"
  shows "size (A #\<union> B) = size A + size B"
  using assms size_Un_Int [of A B] by simp

lemma size_Diff_subset_Int:
  shows "size (\<Sigma> - \<Sigma>') = size \<Sigma> - size (\<Sigma> #\<inter> \<Sigma>')"
proof -
  have "\<Sigma> - \<Sigma>' = \<Sigma> - \<Sigma> #\<inter> \<Sigma>'" by (auto simp add: multiset_eq_iff)
  thus ?thesis by (simp add: size_Diff_submset)
qed

lemma diff_size_le_size_Diff:  "size (\<Sigma>:: _ multiset) - size \<Sigma>' \<le> size (\<Sigma> - \<Sigma>')"
proof-
  have "size \<Sigma> - size \<Sigma>' \<le> size \<Sigma> - size (\<Sigma> #\<inter> \<Sigma>')" using size_mset_mono diff_le_mono2 subset_mset.inf_le2 by blast
  also have "\<dots> = size(\<Sigma>-\<Sigma>')" using assms by(simp add: size_Diff_subset_Int)
  finally show ?thesis .
qed

lemma size_Diff1_less: "x\<in># \<Sigma> \<Longrightarrow> size (\<Sigma> - {#x#}) < size \<Sigma>"
  apply (rule Suc_less_SucD)
  by (simp add: size_Suc_Diff1)

lemma size_Diff2_less: "x\<in># \<Sigma> \<Longrightarrow> y\<in># \<Sigma> \<Longrightarrow> size (\<Sigma> - {#x#} - {#y#}) < size \<Sigma>"
  using nonempty_has_size by (fastforce intro!: diff_Suc_less simp add: size_Diff1_less size_Diff_subset_Int mset_inter_single)

lemma size_Diff1_le: "size (\<Sigma> - {#x#}) \<le> size \<Sigma>"
  apply (case_tac "x \<in># \<Sigma>")
  by (simp_all add: size_Diff1_less less_imp_le)

lemma size_psubset: "(\<Sigma>:: _ multiset) \<le># \<Sigma>' \<Longrightarrow> size \<Sigma> < size \<Sigma>' \<Longrightarrow> \<Sigma> <# \<Sigma>'"
  using less_irrefl subset_mset_def by blast


subsection {* Multiset Extension of Multiset Ordering *}

text {*
The @{text "op #\<subset>##"} and @{text "op #\<subseteq>##"} operators are introduced as the multiset extension of
the multiset orderings of @{term "op #\<subset>#"} and @{term "op #\<subseteq>#"}.
*}

definition
  less_mset_mset :: "('a :: order) multiset multiset \<Rightarrow> 'a multiset multiset \<Rightarrow> bool" (infix "#<##" 50)
where
  "M' #<## M \<longleftrightarrow> (M', M) \<in> mult {(x', x). x' #<# x}"

definition
  le_mset_mset :: "('a :: order) multiset multiset \<Rightarrow> 'a multiset multiset \<Rightarrow> bool" (infix "#<=##" 50)
where
  "M' #<=## M \<longleftrightarrow> M' #<## M \<or> M' = M"

notation (xsymbols) less_mset_mset (infix "#\<subset>##" 50)
notation (xsymbols) le_mset_mset (infix "#\<subseteq>##" 50)

lemmas less_mset_mset\<^sub>D\<^sub>M = order.mult\<^sub>D\<^sub>M[OF order_multiset, folded less_mset_mset_def]
lemmas less_mset_mset\<^sub>H\<^sub>O = order.mult\<^sub>H\<^sub>O[OF order_multiset, folded less_mset_mset_def]

interpretation multiset_multiset_order: order
  "le_mset_mset :: ('a :: linorder) multiset multiset \<Rightarrow> ('a :: linorder) multiset multiset \<Rightarrow> bool"
  "less_mset_mset :: ('a :: linorder) multiset multiset \<Rightarrow> ('a :: linorder) multiset multiset \<Rightarrow> bool"
  unfolding less_mset_mset_def[abs_def] le_mset_mset_def[abs_def] less_multiset_def[abs_def]
  by (rule order.order_mult)+ default

interpretation multiset_multiset_linorder: linorder
  "le_mset_mset :: ('a :: linorder) multiset multiset \<Rightarrow> ('a :: linorder) multiset multiset \<Rightarrow> bool"
  "less_mset_mset :: ('a :: linorder) multiset multiset \<Rightarrow> ('a :: linorder) multiset multiset \<Rightarrow> bool"
  unfolding less_mset_mset_def[abs_def] le_mset_mset_def[abs_def]
  by (rule linorder.linorder_mult[OF linorder_multiset])

lemma wf_less_mset_mset: "wf {(\<Sigma> :: ('a :: wellorder) multiset multiset, T). \<Sigma> #\<subset>## T}"
  unfolding less_mset_mset_def by (auto intro: wf_mult wf_less_multiset)

interpretation multiset_multiset_wellorder: wellorder
  "le_mset_mset :: ('a :: wellorder) multiset multiset \<Rightarrow> ('a :: wellorder) multiset multiset \<Rightarrow> bool"
  "less_mset_mset :: ('a :: wellorder) multiset multiset \<Rightarrow> ('a :: wellorder) multiset multiset \<Rightarrow> bool"
  by unfold_locales (blast intro: wf_less_mset_mset[unfolded wf_def, rule_format])

lemma union_less_mset_mset_mono2: "B #\<subset>## D ==> C + B #\<subset>## C + (D::'a::order multiset multiset)"
apply (unfold less_mset_mset_def mult_def)
apply (erule trancl_induct)
 apply (blast intro: mult1_union)
apply (blast intro: mult1_union trancl_trans)
done

lemma union_less_mset_mset_diff_plus:
  "U \<le># \<Sigma> \<Longrightarrow> T #\<subset>## U \<Longrightarrow> \<Sigma> - U + T #\<subset>## \<Sigma>"
  apply (drule subset_mset.diff_add[symmetric])
  using union_less_mset_mset_mono2[of T U "\<Sigma> - U"] by simp


lemma ex_gt_imp_less_mset_mset:
  "(\<exists>y :: 'a :: linorder multiset \<in># T. (\<forall>x. x \<in># \<Sigma> \<longrightarrow> x #\<subset># y)) \<Longrightarrow> \<Sigma> #\<subset>## T"
  using less_mset_mset\<^sub>H\<^sub>O by force

subsection {* Multiset and set conversion*}
lemma mset_set_set_mset_empty_mempty[iff]:
  "mset_set (set_mset D) = {#} \<longleftrightarrow> D = {#}"
  by (auto dest: arg_cong[of _ _ set_mset])

lemma count_mset_0[iff]: "count (mset D) L = 0 \<longleftrightarrow> L \<notin> set D"
  by (metis in_multiset_in_set not_gr0)

end
