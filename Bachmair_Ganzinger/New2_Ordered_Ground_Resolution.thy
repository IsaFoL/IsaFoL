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

abbreviation "side_clause \<equiv> (\<lambda>(C,As). C + poss As)"
abbreviation "side_clauses Cs \<equiv> mset (map side_clause Cs)"
abbreviation "main_clause \<equiv> (\<lambda>(D,As). D + negs (mset As))"


(* "'b" abbreviates "'a multiset" and "'a list" *)
abbreviation get_C :: "'a clause * 'b \<Rightarrow> 'a clause" where 
  "get_C \<equiv> fst"

abbreviation get_As :: "'a clause * 'b \<Rightarrow> 'b" where 
  "get_As \<equiv> snd"


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
abbreviation "str_maximal_in A CAis \<equiv> (\<forall>B \<in> atms_of (get_C CAis). B < A)"

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
  
abbreviation(output) "Union_Cs CAs \<equiv> \<Union># (mset (map get_C CAs))"
  
inductive 
  ord_resolve :: "'a side_clause list \<Rightarrow> 'a main_clause \<Rightarrow> 'a clause \<Rightarrow> bool"
  where
   ord_resolve:
   "length CAs = length As \<Longrightarrow> 
    CAs \<noteq> [] \<Longrightarrow> 
    As \<noteq> [] \<Longrightarrow>
    \<forall>i. i < length CAs \<longrightarrow> get_As (CAs ! i) \<noteq> {#} \<Longrightarrow>
    \<forall>i. i < length CAs \<longrightarrow> (\<forall>Ai \<in># get_As (CAs ! i). Ai = As ! i) \<Longrightarrow>
    eligible (D,As) \<Longrightarrow>
    \<forall>i. i < length CAs \<longrightarrow> str_maximal_in (As ! i) (CAs ! i) \<Longrightarrow>
    \<forall>C \<in> set CAs. S (side_clause C) = {#} \<Longrightarrow>
    ord_resolve CAs (D,As) (Union_Cs CAs + D)"

lemma ord_resolve_sound:
  assumes
    res_e: "ord_resolve CAs (D,As) E" and
    cc_true: "I \<Turnstile>m side_clauses CAs" and
    d_true: "I \<Turnstile> main_clause (D,As)"
  shows "I \<Turnstile> E"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve)
  have e: "E = Union_Cs CAs + D" using ord_resolve(1) .
  have cs_as_len: "length CAs = length As" using ord_resolve(2) .
  have cs_ne: "\<forall>i<length CAs. get_As (CAs ! i) \<noteq> {#}" using ord_resolve(5) .
  have a_eq: "\<forall>i<length CAs. \<forall>Ai\<in>#get_As (CAs ! i). Ai = As ! i" using ord_resolve(6) .

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
      c_in_cs: "i < length CAs" and 
      a_false: "As ! i \<notin> I"
      using ord_resolve(2) by (metis in_set_conv_nth)
    have c_cf': "set_mset (side_clause (CAs ! i)) \<subseteq> set_mset (\<Union># (side_clauses CAs))" (* Kind of ugly *)
      using c_in_cs
      by (metis (no_types, lifting) in_Union_mset_iff length_map nth_map nth_mem_mset subsetI)
    let ?Ai = "poss (get_As (CAs ! i))"
    have "\<not> I \<Turnstile> ?Ai" 
      using a_false a_eq cs_ne c_in_cs unfolding true_cls_def by auto
    moreover have "I \<Turnstile> side_clause (CAs ! i)" 
      using c_in_cs cc_true unfolding true_cls_mset_def by auto
    ultimately have "I \<Turnstile> get_C (CAs ! i)"
      by (simp add: prod.case_eq_if) 
    then show ?thesis using c_in_cs unfolding e true_cls_def
      by fastforce 
  qed
qed

lemma filter_neg_atm_of_S: "{#Neg (atm_of L). L \<in># S C#} = S C" (* Do I use this? *)
  by (rule trans[OF image_mset_cong[of "S C" "\<lambda>L. Neg (atm_of L)" id]])
    (auto intro!: S_selects_neg_lits)


text {*
This corresponds to Lemma 3.13:
*}

lemma ord_resolve_reductive:
  assumes res_e: "ord_resolve CAs (D,As) E"
  shows "E < main_clause (D,As)"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve)
  define UCAs where "UCAs = Union_Cs CAs"
  have e: "E = UCAs + D" unfolding UCAs_def using ord_resolve(1) .
  have cs_as_len: "length CAs = length As" using ord_resolve(2) .
  have as_ne: "As \<noteq> []" using ord_resolve(4) .
  
  show ?thesis
  proof (cases "UCAs = {#}")
    case True
    have "negs (mset As) \<noteq> {#}"
       using as_ne by auto
    thus ?thesis
       unfolding True e by auto
  next
    case False
    moreover
    define max_A_of_Cs where "max_A_of_Cs = Max (atms_of UCAs)"
    ultimately have
      mc_in: "max_A_of_Cs \<in> atms_of UCAs" and 
      mc_max: "\<And>B. B \<in> atms_of UCAs \<Longrightarrow> B \<le> max_A_of_Cs"
      by auto
    
    then have "\<exists>C_max \<in> set CAs. max_A_of_Cs \<in> atms_of (get_C C_max)"
      unfolding UCAs_def by (induction CAs) auto
    then obtain max_i where
        cm_in_cas: "max_i < length CAs" and
        mc_in_cm: "max_A_of_Cs \<in> atms_of (get_C (CAs ! max_i))"
      by (metis in_set_conv_nth)
    define CA_max where "CA_max = CAs ! max_i"
    define A_max where "A_max = As ! max_i"
    define C_max where "C_max = get_C CA_max"
    have mc_lt_ma: "max_A_of_Cs < A_max"
      unfolding A_max_def using ord_resolve(8) cm_in_cas mc_in_cm by auto
    
    hence ucas_ne_neg_aa: "UCAs \<noteq> negs (mset As)"
      using mc_in mc_max mc_lt_ma cm_in_cas cs_as_len unfolding A_max_def
      by (metis atms_of_negg nth_mem set_mset_mset leD)
    
    moreover have ucas_lt_ma: "\<forall>B \<in> atms_of UCAs. B < A_max"
      using mc_max mc_lt_ma by fastforce
    moreover have "\<not>Neg A_max \<in># UCAs"
      using ucas_lt_ma neg_lit_in_atms_of by fastforce
    moreover have "Neg A_max \<in># negs (mset As)"
      using cm_in_cas cs_as_len A_max_def by auto
    ultimately have "UCAs < negs (mset As)"
      unfolding less_multiset\<^sub>H\<^sub>O
      apply (auto simp: ucas_ne_neg_aa not_in_iff intro!: exI[of _ "Neg A_max"])
      (* TODO tune proof *)
      using atms_less_eq_imp_lit_less_eq_neg count_inI dual_order.strict_implies_order 
          gr_implies_not_zero order.not_eq_order_implies_strict by metis
    then show ?thesis unfolding e by auto
  qed
qed
    
