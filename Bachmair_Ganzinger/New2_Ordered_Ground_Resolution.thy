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
  eligible:
  "S (main_clause (D,As)) = negs (mset As) 
   \<or> 
   (
     S (main_clause (D,As)) = {#} 
     \<and> length As = 1 
     \<and> As ! 0 = Max (atms_of (main_clause (D,As)))
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
    
    hence "\<exists>C_max \<in> set CAs. max_A_of_Cs \<in> atms_of (get_C C_max)"
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

text {*
This corresponds to Theorem 3.15:
*}

theorem ord_resolve_counterex_reducing:
  assumes
    ec_ni_n: "{#} \<notin> N" and
    d_in_n: "DA \<in> N" and
    d_cex: "\<not> INTERP N \<Turnstile> DA" and
    d_min: "\<And>C. C \<in> N \<Longrightarrow> \<not> INTERP N \<Turnstile> C \<Longrightarrow> DA \<le> C"
  obtains CAs E D As where
    "main_clause (D,As) = DA" (* This line was added to fit the new definition. It does not look so nice... *)
    "set_mset (side_clauses CAs) \<subseteq> N"
    "INTERP N \<Turnstile>m side_clauses CAs"
    "\<And>CA. CA \<in># side_clauses CAs \<Longrightarrow> productive N CA"
    "ord_resolve CAs (D,As) E"
    "\<not> INTERP N \<Turnstile> E"
    "E < DA"
proof -
  have d_ne: "DA \<noteq> {#}"
    using d_in_n ec_ni_n by blast
  have "\<exists>D As. DA = main_clause (D,As) \<and> As \<noteq> [] \<and> negs (mset As) \<le># DA \<and> eligible (D,As)"
  proof (cases "S DA = {#}")
    assume s_d_e: "S DA = {#}"
    define A where "A = Max (atms_of DA)"
    define As where "As = [A]"
    define D where "D = DA-{#Neg A #}"
    
    have na_in_d: "Neg A \<in># DA"
      unfolding A_def using s_d_e d_ne d_in_n d_cex d_min
      by (metis Max_in_lits Max_lit_eq_pos_or_neg_Max_atm max_pos_imp_true_in_Interp
        true_Interp_imp_INTERP)
    hence das: "DA = main_clause (D,As)" unfolding D_def As_def by auto
    moreover
    from na_in_d have "negs (mset As) \<subseteq># DA"
      by (simp add: As_def) 
    moreover
    have "As ! 0 = Max (atms_of (main_clause (D, As)))"
      using A_def As_def das by auto
    hence "eligible (D, As)" using eligible s_d_e As_def das by auto
    ultimately show ?thesis using As_def by blast
  next
    assume s_d_e: "S DA \<noteq> {#}"
    define As where "As = list_of_mset {#atm_of L. L \<in># S DA#}"
    define D where "D = DA - negs {#atm_of L. L \<in># S DA#}"
    
    have "As \<noteq> []" unfolding As_def using s_d_e
      by (metis image_mset_is_empty_iff list_of_mset_empty)
    moreover
    have da_sub_as: "negs {#atm_of L. L \<in># S DA#} \<subseteq># DA" 
      using S_selects_subseteq by (auto simp: filter_neg_atm_of_S)
    hence "negs (mset As) \<subseteq># DA" unfolding As_def by auto
    moreover
    have das: "DA = main_clause (D, As)" using da_sub_as unfolding D_def As_def by auto
    moreover
    have "S DA = negs {#atm_of L. L \<in># S DA#}" 
      by (auto simp: filter_neg_atm_of_S)
    hence "S DA = negs (mset As)" unfolding As_def by auto
    hence "eligible (D, As)" unfolding das using eligible by auto
    ultimately show ?thesis by blast
  qed
  then obtain D As where
    da_da: "DA = main_clause (D,As)" and
    as_ne: "As \<noteq> []" and 
    negs_as_le_d: "negs (mset As) \<le># DA" and
    s_d: "eligible (D,As)"
    by blast
  have "set As \<subseteq> INTERP N"
    using d_cex negs_as_le_d by force
  hence prod_ex: "\<forall>A \<in> set As. \<exists>D. produces N D A"
    unfolding INTERP_def  
    by (metis (no_types, lifting) INTERP_def subsetCE UN_E not_produces_imp_notin_production) 
  hence "\<And>A. \<exists>D. produces N D A \<longrightarrow> A \<in> set As"
    using ec_ni_n by (auto intro: productive_in_N)
  hence "\<And>A. \<exists>D. produces N D A \<longleftrightarrow> A \<in> set As"
    using prod_ex by blast
  then obtain C_of where c_of0: "\<And>A. produces N (C_of A) A \<longleftrightarrow> A \<in> set As"
    by metis
  hence prod_c0: "\<forall>A \<in> set As. produces N (C_of A) A"
    by blast
  
  define C'_of where "C'_of \<equiv> \<lambda>A. {#L \<in># C_of A. L \<noteq> Pos A#}"
  define M_of where "M_of \<equiv> \<lambda>A. count (C_of A) (Pos A)"
  
  have d_of: "C_of = (\<lambda>A. C'_of A + replicate_mset (M_of A) (Pos A))"
    unfolding C'_of_def M_of_def
    by (rule ext) (metis add.commute filter_eq_replicate_mset multiset_partition)
  have m_nz: "\<And>A. A \<in> set As \<Longrightarrow> M_of A \<noteq> 0"
    using prod_c0 unfolding M_of_def by (auto intro: produces_imp_Pos_in_lits)
  
  define CAs where "CAs = map (\<lambda>A. (C'_of A, replicate_mset (M_of A) A)) As" 
  {
    fix CA
    assume "CA \<in> set CAs"
    then obtain i where i_p: "i < length CAs" "CAs ! i = CA"
      by (meson in_set_conv_nth)
    let ?A = "As ! i"
    have "production N (C_of (As ! i)) = {As ! i}" using i_p CAs_def prod_c0 by auto 
    then have "productive N (side_clause CA)" using i_p CAs_def
      using d_of by auto 
  }
  then have prod_c': "\<And>CA. CA \<in> set CAs \<Longrightarrow> productive N (side_clause CA)" .
  then have prod_c: "\<And>CA. CA \<in># side_clauses CAs \<Longrightarrow> productive N CA" by auto
  hence cs_subs_n: "set_mset (side_clauses CAs) \<subseteq> N"
    using productive_in_N by auto
  have cs_true: "INTERP N \<Turnstile>m side_clauses CAs"
    unfolding true_cls_mset_def using prod_c productive_imp_true_in_INTERP by auto
    
  have "\<And>A. A \<in> set As \<Longrightarrow> \<not> Neg A \<in># C_of A"
    using prod_c0 produces_imp_neg_notin_lits by auto
  hence a_ni_c': "\<And>A. A \<in> set As \<Longrightarrow> A \<notin> atms_of (C'_of A)"
    unfolding C'_of_def using atm_imp_pos_or_neg_lit by force
  have c'_le_c: "\<And>A. C'_of A \<le> C_of A"
    unfolding C'_of_def by (auto intro: subset_eq_imp_le_multiset)
  have a_max_c: "\<And>A. A \<in> set As \<Longrightarrow> A = Max (atms_of (C_of A))"
    using prod_c0 productive_imp_produces_Max_atom[of N] by auto
  hence "\<And>A. A \<in> set As \<Longrightarrow> C'_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (C'_of A)) \<le> A"
    using c'_le_c by (metis less_eq_Max_atms_of)
  moreover have "\<And>A. A \<in> set As \<Longrightarrow> C'_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (C'_of A)) \<noteq> A"
    using a_ni_c' Max_in by (metis (no_types) atms_empty_iff_empty finite_atms_of)
  ultimately have max_c'_lt_a: "\<And>A. A \<in> set As \<Longrightarrow> C'_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (C'_of A)) < A"
    by (metis order.strict_iff_order)
  
  have le_cs_as: "length CAs = length As"  unfolding CAs_def by simp
  moreover
  have "CAs \<noteq> []" using as_ne le_cs_as by auto 
  moreover
  have "As \<noteq> []" using as_ne .
  moreover
  have "\<forall>i. i < length CAs \<longrightarrow> get_As (CAs ! i) \<noteq> {#}"
    unfolding CAs_def
    using m_nz by simp
  moreover
  have " \<forall>i. i < length CAs \<longrightarrow> (\<forall>Ai \<in># get_As (CAs ! i). Ai = As ! i)"
    unfolding CAs_def by auto
  moreover
  have "eligible (D,As)" using s_d by blast 
  moreover
  have "\<And>x B. production N (C_of x) = {x} \<Longrightarrow> B \<in># C_of x \<Longrightarrow> B \<noteq> Pos x \<Longrightarrow> atm_of B < x" 
    by (metis atm_of_lit_in_atms_of insert_not_empty le_imp_less_or_eq Pos_atm_of_iff
          Neg_atm_of_iff pos_neg_in_imp_true produces_imp_Pos_in_lits produces_imp_atms_leq
          productive_imp_false_interp)
  then have "\<forall>i. i < length CAs \<longrightarrow> (\<forall>B\<in>atms_of (get_C (CAs ! i)). B < As ! i)"
    using CAs_def prod_c0 by (auto simp: C'_of_def atms_of_def intro: produces_imp_Max_atom)
  then have "\<And>i. i < length CAs \<Longrightarrow> str_maximal_in (As ! i) (CAs ! i)" by metis
  moreover
  have "\<forall>C \<in> set CAs. S (side_clause C) = {#}"
    using prod_c' producesD productive_imp_produces_Max_literal by blast 
  ultimately have res_e: "ord_resolve CAs (D,As) (Union_Cs CAs + D)" using ord_resolve by auto
  
  have "\<And>A. A \<in> set As \<Longrightarrow> \<not> interp N (C_of A) \<Turnstile> C_of A"
    by (simp add: prod_c0 producesD)
  hence "\<And>A. A \<in> set As \<Longrightarrow> \<not> Interp N (C_of A) \<Turnstile> C'_of A"
    unfolding prod_c0 C'_of_def Interp_def true_cls_def 
    using true_lit_def not_gr_zero
    using prod_c0 by auto 
  hence c'_at_n: "\<And>A. A \<in> set As \<Longrightarrow> \<not> INTERP N \<Turnstile> C'_of A"
    using a_max_c c'_le_c max_c'_lt_a false_Interp_imp_INTERP unfolding true_cls_def
    by (metis true_cls_def true_cls_empty)
  have "\<not> INTERP N \<Turnstile> Union_Cs CAs"
    unfolding CAs_def true_cls_def by (auto dest!: c'_at_n)
  moreover have "\<not> INTERP N \<Turnstile> D"
    using d_cex unfolding da_da by simp
  ultimately have e_cex: "\<not> INTERP N \<Turnstile> Union_Cs CAs + D"
    by simp
    
  have "main_clause (D,As) = DA" using da_da by simp
  moreover
  have "set_mset (side_clauses CAs) \<subseteq> N" using cs_subs_n by auto
  moreover
  have "INTERP N \<Turnstile>m side_clauses CAs" using cs_true by auto
  moreover
  have "\<And>CA. CA \<in># side_clauses CAs \<Longrightarrow> productive N CA" using prod_c by auto
  moreover
  have "ord_resolve CAs (D,As) (Union_Cs CAs + D)" using res_e .
  moreover
  have "\<not> INTERP N \<Turnstile> Union_Cs CAs + D" using e_cex by auto
  moreover
  have "Union_Cs CAs + D < DA"
    using res_e ord_resolve_reductive da_da by metis
  ultimately
  show ?thesis ..
  
  (* You can trim a lot in this proof *)
qed

lemma ord_resolve_atms_of_concl_subset:
  assumes res_e: "ord_resolve CAs (D,As) E"
  shows "atms_of E \<subseteq> (\<Union>C \<in> set_mset (side_clauses CAs). atms_of C) \<union> atms_of (main_clause (D,As))"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve)
  have e: "E = \<Union>#mset (map get_C CAs) + D" using ord_resolve(1) .
  have "atms_of (Union_Cs CAs) \<subseteq> (\<Union>C\<in>set_mset (side_clauses CAs). atms_of C)"
     by (auto simp: atms_of_def)
  moreover have "atms_of D \<subseteq> atms_of (main_clause (D,As))"
    by simp
  ultimately show ?thesis
    unfolding e by auto
qed

end

end
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
    
