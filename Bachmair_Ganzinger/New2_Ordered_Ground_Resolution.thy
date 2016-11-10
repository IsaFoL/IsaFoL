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
    ord_resolve Cs (D,As) (\<Union># {#fst C. C \<in># mset Cs#} + D)"

lemma ord_resolve_sound:
  assumes
    res_e: "ord_resolve Cs (D,As) E" and
    cc_true: "I \<Turnstile>m side_clauses Cs" and
    d_true: "I \<Turnstile> main_clause (D,As)"
  shows "I \<Turnstile> E"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve)
  have e: "E = \<Union># {#fst C. C \<in># mset Cs#} + D" using ord_resolve(1) .
  have cs_as_len: "length Cs = length As" using ord_resolve(2) .
  have cs_ne: "\<forall>i<length Cs. snd (Cs ! i) \<noteq> {#}" using ord_resolve(5) .
  have a_eq: "\<forall>i<length Cs. \<forall>Ai\<in>#snd (Cs ! i). Ai = As ! i" using ord_resolve(6) .

  show ?thesis
  proof (cases "\<forall>A \<in> set As. A\<in>I")
    case True
    hence "\<not> I \<Turnstile> negs (mset As)"
      unfolding true_cls_def by fastforce
    hence "I \<Turnstile> D"
      using d_true by fast
    then show ?thesis unfolding e by blast
  next
    case False
    then obtain i where 
      a_in_aa: "i < length As" and 
      c_in_cs: "i < length Cs" and 
      a_false: "As ! i \<notin> I"
      using ord_resolve(2) by (metis in_set_conv_nth)
    have c_cf': "set_mset (side_clause (Cs ! i)) \<subseteq> set_mset (\<Union># (side_clauses Cs))" (* Kind of ugly *)
      using c_in_cs
      by (metis (no_types, lifting) in_Union_mset_iff length_map nth_map nth_mem_mset subsetI)
    let ?Ai = "poss (snd (Cs ! i))"
    have "\<not> I \<Turnstile> ?Ai" 
      using a_false a_eq cs_ne c_in_cs unfolding true_cls_def by auto
    moreover have "I \<Turnstile> side_clause (Cs ! i)" 
      using c_in_cs cc_true unfolding true_cls_mset_def by auto
    ultimately have "I \<Turnstile> fst (Cs ! i)"
      by (simp add: prod.case_eq_if) 
    then show ?thesis using c_in_cs unfolding e true_cls_def
      by fastforce 
  qed
qed

lemma filter_neg_atm_of_S: "{#Neg (atm_of L). L \<in># S C#} = S C" (*Do I use this? *)
  by (rule trans[OF image_mset_cong[of "S C" "\<lambda>L. Neg (atm_of L)" id]])
    (auto intro!: S_selects_neg_lits)


text {*
This corresponds to Lemma 3.13:
*}

lemma ord_resolve_reductive:
  assumes res_e: "ord_resolve Cs (D,As) E"
  shows "E < main_clause (D,As)"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve)
  
  show ?thesis
  proof (cases "Cs = []")
    case True
    have "negs (mset As) \<noteq> {#}"
      sorry
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
qed
    
