(*  Title:       Ordered Ground Resolution with Selection
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section {* Ordered Ground Resolution with Selection *}

theory New2_Ordered_Ground_Resolution
imports Inference_System Ground_Resolution_Model Multiset_Even_More
begin


text {*
Ordered ground resolution with selection is the second inference system studied in Section 3
(``Standard Resolution'') of Bachmair and Ganzinger's chapter.
*}


subsection {* Inference Rule *}

text {*
Ordered ground resolution consists of a single rule, called @{text ord_resolve} below. Like
@{text unord_resolve}, the rule is sound and counterexample-reducing. In addition, it is reductive.
*}

subsection {* Main and side clauses *} (* Should maybe be in Clausal_Logic *)

type_synonym 'a side_clause = "'a clause * 'a multiset"
type_synonym 'a main_clause = "'a clause * 'a list"

abbreviation "side_clause \<equiv> (\<lambda>(C,A). C + {#Pos Atm. Atm \<in># A #})"
abbreviation "side_clauses Cs \<equiv> mset (map side_clause Cs)"
abbreviation "main_clause \<equiv> (\<lambda>(D,A). D + {#Neg Atm. Atm \<in># mset A#})"


context ground_resolution_with_selection
begin

text {*
The following inductive definition corresponds to Figure 2. A slight difference is that the figure
appears to treat the side premises as a list, whereas here they are more conveniently seen as a
multiset.

\begin{nit}
References to $S(D)$ should have been to $S(\lnot\,A_1 \lor \cdots \lor \lnot\,A_n \lor D)$.
In condition (iii), it is not clear with respect to which clause the ``selected atom'' must be
seen. The two candidates are $S(\lnot\,A_1 \lor \cdots \lor \lnot\,A_n \lor D)$ or
$S(C_i \lor A_i \lor \cdots \lor A_i)$. Apparently, the latter was meant.
\end{nit}
*}

abbreviation "maximal_in A DAs \<equiv> (A = Max (atms_of (main_clause DAs)))"
abbreviation "str_maximal_in A CAis \<equiv> (\<forall>B \<in> atms_of (fst CAis). B < A)"

(* Inspiration from supercalc *)
inductive eligible :: "'a main_clause \<Rightarrow> bool" where
  "S (main_clause (D,As)) = negs (mset As) 
   \<or> 
   (
     S (main_clause (D,As)) = {#} 
     \<and> length As = 1 
     \<and> As ! 1 = Max (atms_of (main_clause (D,As)))
   )
   \<Longrightarrow> eligible (D,As)"

inductive 
  ord_resolve :: "'a side_clause list \<Rightarrow> 'a main_clause \<Rightarrow> 'a clause \<Rightarrow> bool"
  where
   ord_resolve:
   "length Cs = length As \<Longrightarrow> 
    length Cs > 0 \<Longrightarrow> 
    length As > 0 \<Longrightarrow>
    \<forall>i. i < length Cs \<longrightarrow> snd (Cs ! i) \<noteq> {#} \<Longrightarrow>
    \<forall>i. i < length Cs \<longrightarrow> (\<forall>Ai \<in># snd (Cs ! i). Ai = As ! i) \<Longrightarrow>
    eligible (D,As) \<Longrightarrow>
    \<forall>i. i < length Cs \<longrightarrow> str_maximal_in (As ! i) (Cs ! i) \<Longrightarrow>
    \<forall>C \<in> set Cs. S (side_clause C) = {#} \<Longrightarrow>
    ord_resolve Cs (D,As) ((\<Union># (mset (map fst Cs))) + D)"

lemma ord_resolve_sound:
  assumes
    res_e: "ord_resolve Cs (D,As) E" and
    cc_true: "I \<Turnstile>m side_clauses Cs" and
    d_true: "I \<Turnstile> main_clause (D,As)"
  shows "I \<Turnstile> E"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve)
  show ?thesis sorry
qed

end
