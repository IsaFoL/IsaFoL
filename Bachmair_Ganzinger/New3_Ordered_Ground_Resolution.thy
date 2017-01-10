(*  Title:       Ordered Ground Resolution with Selection
    Author:      Anders Schlichtkrull, 2017
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Anders Schlichtkrull <jasmin.blanchette at inria.fr>
*)

section {* Ordered Ground Resolution with Selection *}

theory New3_Ordered_Ground_Resolution
imports Inference_System Ground_Resolution_Model Multiset_Even_More Clauses Map2
begin

(* Perhaps this will improve automation? *)
declare nth_equalityI[simp]

text {*
Ordered ground resolution with selection is the second inference system studied in Section 3
(``Standard Resolution'') of Bachmair and Ganzinger's chapter.
*}


subsection {* Inference Rule *}

text {*
Ordered ground resolution consists of a single rule, called @{text ord_resolve} below. Like
@{text unord_resolve}, the rule is sound and counterexample-reducing. In addition, it is reductive.
*}


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

abbreviation "maximal_in A DAs \<equiv> (A = Max (atms_of DAs))"
definition "str_maximal_in A CAis \<equiv> (\<forall>B \<in> atms_of CAis. B < A)"

(* Inspiration from supercalc *)
inductive eligible :: "'a list \<Rightarrow> 'a clause \<Rightarrow> bool" where
  eligible:
  "S DAi = negs (mset Ai) 
   \<or> 
   (
     S DAi = {#} 
     \<and> length Ai = 1 
     \<and> maximal_in (Ai ! 0) DAi
   )
   \<Longrightarrow> eligible Ai DAi"
  
inductive 
  ord_resolve :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool"
  where
   ord_resolve:
   "length (CAi :: 'a clause list) = n \<Longrightarrow>
    length (Ci  :: 'a clause list) = n \<Longrightarrow>
    length (Aij :: 'a multiset list) = n \<Longrightarrow> (* Maybe a clause list, would be better?*)
    length (Ai  :: 'a list) = n \<Longrightarrow>
    n \<noteq> 0 \<Longrightarrow>
    \<forall>i < n. (CAi ! i) = (Ci ! i + (poss (Aij ! i))) \<Longrightarrow>
    \<forall>i < n. Aij ! i \<noteq> {#} \<Longrightarrow>
    \<forall>i < n. (\<forall>A \<in># Aij ! i. A = Ai ! i) \<Longrightarrow>
    eligible Ai (D + negs (mset Ai)) \<Longrightarrow>
    \<forall>i < n. str_maximal_in (Ai ! i) (Ci ! i) \<Longrightarrow>
    ord_resolve CAi (D + negs (mset Ai)) ((\<Union># (mset Ci)) + D)" 
          
lemma ord_resolve_sound:
  assumes
    res_e: "ord_resolve CAi DAi E" and
    cc_true: "I \<Turnstile>m mset CAi" and
    d_true: "I \<Turnstile> DAi"
  shows "I \<Turnstile> E"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Ci Aij Ai D)
  have dai: "DAi = D + negs (mset Ai)" using ord_resolve by -
  have e: "E = (\<Union># (mset Ci)) + D" using ord_resolve by -
  have cai_len: "length CAi = n" using ord_resolve by -
  have ci_len: "length Ci = n" using ord_resolve by -
  have ai_len: "length Ai = n" using ord_resolve by -
  have cai: "\<forall>i<n. CAi ! i = Ci ! i + poss (Aij ! i) " using ord_resolve by -
  have cs_ne: "\<forall>i<n. Aij ! i \<noteq> {#}" using ord_resolve by -
  have a_eq: "\<forall>i<n. \<forall>A\<in>#Aij ! i. A = Ai ! i " using ord_resolve by -
      
  have cs_as_len: "length CAi = length Ai" using cai_len ai_len by auto

  show ?thesis
  proof (cases "\<forall>A \<in> set Ai. A\<in>I")
    case True
    hence "\<not> I \<Turnstile> negs (mset Ai)"
      unfolding true_cls_def by fastforce
    hence "I \<Turnstile> D"
      using d_true dai by fast
    then show ?thesis unfolding e by blast
  next
    case False
    then obtain i where 
      a_in_aa: "i < n" and
      a_false: "Ai ! i \<notin> I"
      using cs_as_len cai_len by (metis in_set_conv_nth)
    let ?Ai = "poss (Aij ! i)"
    have "\<not> I \<Turnstile> ?Ai" 
      using a_false a_eq cs_ne a_in_aa unfolding true_cls_def by auto
    moreover have "I \<Turnstile> CAi ! i" 
      using a_in_aa cc_true unfolding true_cls_mset_def using cai_len by auto
    ultimately have "I \<Turnstile> Ci ! i"
      using cai a_in_aa by auto
    then show ?thesis using a_in_aa ci_len unfolding e true_cls_def
      by (meson in_Union_mset_iff nth_mem_mset union_iff)
  qed
qed

lemma filter_neg_atm_of_S: "{#Neg (atm_of L). L \<in># S C#} = S C" (* Do I use this? *)
  by (rule trans[OF image_mset_cong[of "S C" "\<lambda>L. Neg (atm_of L)" id]])
    (auto intro!: S_selects_neg_lits)


text {*
This corresponds to Lemma 3.13:
*}

lemma ord_resolve_reductive:
  assumes res_e: "ord_resolve CAi DAi E"
  shows "E < DAi"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Ci Aij Ai D)
  have dai: "DAi = D + negs (mset Ai)" using ord_resolve by -
  have e: "E = \<Union>#mset Ci + D" using ord_resolve by -
  have cai_len: "length CAi = n" using ord_resolve by -
  have ci_len: "length Ci = n" using ord_resolve by -
  have ai_len: "length Ai = n" using ord_resolve by -
  have nz: "n \<noteq> 0" using ord_resolve by -
  have cai: "\<forall>i<n. CAi ! i = Ci ! i + poss (Aij ! i) " using ord_resolve by -
  
  have maxim: " \<forall>i<n. str_maximal_in (Ai ! i) (Ci ! i)" using ord_resolve by -
  
  have as_ne: "Ai \<noteq> []" using nz ai_len by auto
  have cs_as_len: "length CAi = length Ai" using cai_len ai_len by auto
  
  show ?thesis
  proof (cases "\<Union>#mset Ci = {#}")
    case True
    have "negs (mset Ai) \<noteq> {#}"
       using as_ne by auto
    thus ?thesis
       unfolding True e dai by auto
  next
    case False
    moreover
    define max_A_of_Cs where "max_A_of_Cs = Max (atms_of (\<Union>#mset Ci))"
    ultimately have
      mc_in: "max_A_of_Cs \<in> atms_of (\<Union>#mset Ci)" and 
      mc_max: "\<And>B. B \<in> atms_of (\<Union>#mset Ci) \<Longrightarrow> B \<le> max_A_of_Cs"
      by auto
    
    hence "\<exists>C_max \<in> set Ci. max_A_of_Cs \<in> atms_of (C_max)"
      by (metis atm_imp_pos_or_neg_lit in_Union_mset_iff neg_lit_in_atms_of pos_lit_in_atms_of set_mset_mset)
    then obtain max_i where
        cm_in_cas: "max_i < length CAi" and
        mc_in_cm: "max_A_of_Cs \<in> atms_of (Ci ! max_i)"
      using in_set_conv_nth[of _ CAi]
      by (metis cai_len ci_len in_set_conv_nth) 
    define CA_max where "CA_max = CAi ! max_i"
    define A_max where "A_max = Ai ! max_i"
    define C_max where "C_max = Ci ! max_i"
    have mc_lt_ma: "max_A_of_Cs < A_max"
      unfolding A_max_def using maxim cm_in_cas mc_in_cm cai_len unfolding str_maximal_in_def by auto
    
    hence ucas_ne_neg_aa: "(\<Union>#mset Ci) \<noteq> negs (mset Ai)"
      using mc_in mc_max mc_lt_ma cm_in_cas cs_as_len unfolding A_max_def
      by (metis atms_of_negg nth_mem set_mset_mset leD)
    
    moreover have ucas_lt_ma: "\<forall>B \<in> atms_of (\<Union>#mset Ci). B < A_max"
      using mc_max mc_lt_ma by fastforce
    moreover have "\<not>Neg A_max \<in># (\<Union>#mset Ci)"
      using ucas_lt_ma neg_lit_in_atms_of[of A_max "\<Union>#mset Ci"] by auto
    moreover have "Neg A_max \<in># negs (mset Ai)"
      using cm_in_cas cs_as_len A_max_def by auto
    ultimately have "(\<Union>#mset Ci) < negs (mset Ai)"
      unfolding less_multiset\<^sub>H\<^sub>O
      apply (auto simp: ucas_ne_neg_aa not_in_iff intro!: exI[of _ "Neg A_max"])
      (* TODO tune proof *)
      using atms_less_eq_imp_lit_less_eq_neg count_inI dual_order.strict_implies_order 
          gr_implies_not_zero order.not_eq_order_implies_strict by metis
    then show ?thesis unfolding e main_clause_def dai by auto
  qed
qed

text {*
This corresponds to Theorem 3.15:
*}

theorem ord_resolve_counterex_reducing:
  assumes
    ec_ni_n: "{#} \<notin> N" and
    d_in_n: "DAi \<in> N" and
    d_cex: "\<not> INTERP N \<Turnstile> DAi" and
    d_min: "\<And>C. C \<in> N \<Longrightarrow> \<not> INTERP N \<Turnstile> C \<Longrightarrow> DAi \<le> C"
  obtains CAi E where
    "set CAi \<subseteq> N"
    "INTERP N \<Turnstile>m mset CAi"
    "\<And>CA. CA \<in> set CAi \<Longrightarrow> productive N CA"
    "ord_resolve CAi DAi E"
    "\<not> INTERP N \<Turnstile> E"
    "E < DAi"
proof -
  have d_ne: "DAi \<noteq> {#}"
    using d_in_n ec_ni_n by blast
  have "\<exists>Ai. Ai \<noteq> [] \<and> negs (mset Ai) \<le># DAi \<and> eligible Ai DAi"
  proof (cases "S DAi = {#}")
    assume s_d_e: "S DAi = {#}"
    define A where "A = Max (atms_of DAi)"
    define Ai where "Ai = [A]"
    define D where "D = DAi-{#Neg A #}"
    
    have na_in_d: "Neg A \<in># DAi"
      unfolding A_def using s_d_e d_ne d_in_n d_cex d_min
      by (metis Max_in_lits Max_lit_eq_pos_or_neg_Max_atm max_pos_imp_true_in_Interp
        true_Interp_imp_INTERP)
    hence das: "DAi = main_clause (D,Ai)" unfolding D_def Ai_def main_clause_def by auto
    moreover
    from na_in_d have "negs (mset Ai) \<subseteq># DAi"
      by (simp add: Ai_def) 
    moreover
    have "Ai ! 0 = Max (atms_of (main_clause (D, Ai)))"
      using A_def Ai_def das by auto
    hence "eligible Ai DAi" using eligible s_d_e Ai_def das by auto
    ultimately show ?thesis using Ai_def by blast
  next
    assume s_d_e: "S DAi \<noteq> {#}"
    define Ai where "Ai = list_of_mset {#atm_of L. L \<in># S DAi#}"
    define D where "D = DAi - negs {#atm_of L. L \<in># S DAi#}"
    
    have "Ai \<noteq> []" unfolding Ai_def using s_d_e
      by (metis image_mset_is_empty_iff list_of_mset_empty)
    moreover
    have da_sub_as: "negs {#atm_of L. L \<in># S DAi#} \<subseteq># DAi" 
      using S_selects_subseteq by (auto simp: filter_neg_atm_of_S)
    hence "negs (mset Ai) \<subseteq># DAi" unfolding Ai_def by auto
    moreover
    have das: "DAi = main_clause (D, Ai)" using da_sub_as unfolding D_def Ai_def main_clause_def by auto
    moreover
    have "S DAi = negs {#atm_of L. L \<in># S DAi#}" 
      by (auto simp: filter_neg_atm_of_S)
    hence "S DAi = negs (mset Ai)" unfolding Ai_def by auto
    hence "eligible Ai DAi" unfolding das using eligible by auto
    ultimately show ?thesis by blast
  qed
  then obtain Ai where
    as_ne: "Ai \<noteq> []" and 
    negs_as_le_d: "negs (mset Ai) \<le># DAi" and
    s_d: "eligible Ai DAi"
    by blast
  define D where "D = DAi - negs (mset Ai)"
  have "set Ai \<subseteq> INTERP N"
    using d_cex negs_as_le_d by force
  hence prod_ex: "\<forall>A \<in> set Ai. \<exists>D. produces N D A"
    unfolding INTERP_def  
    by (metis (no_types, lifting) INTERP_def subsetCE UN_E not_produces_imp_notin_production) 
  hence "\<And>A. \<exists>D. produces N D A \<longrightarrow> A \<in> set Ai"
    using ec_ni_n by (auto intro: productive_in_N)
  hence "\<And>A. \<exists>D. produces N D A \<longleftrightarrow> A \<in> set Ai"
    using prod_ex by blast
  then obtain CA_of where c_of0: "\<And>A. produces N (CA_of A) A \<longleftrightarrow> A \<in> set Ai"
    by metis
  hence prod_c0: "\<forall>A \<in> set Ai. produces N (CA_of A) A"
    by blast
  
  define C'_of where "C'_of \<equiv> \<lambda>A. {#L \<in># CA_of A. L \<noteq> Pos A#}" (* Remove the prime *)
  define Aj_of where "Aj_of \<equiv> \<lambda>A. image_mset atm_of {#L \<in># CA_of A. L = Pos A#}"
  
  have pospos: "\<And>LL A. {#Pos (atm_of x). x \<in># {#L \<in># LL. L = Pos A#}#} = {#L \<in># LL. L = Pos A#}"
    by (metis (mono_tags, lifting) image_filter_cong literal.sel(1) multiset.map_ident)
  have ca_of_c_of_aj_of: "\<And>A. CA_of A = C'_of A + poss (Aj_of A)"
    unfolding C'_of_def Aj_of_def apply auto
    using pospos[of _ "CA_of _"] apply simp
    by (simp add: add.commute multiset_partition)
      
  define n where "n \<equiv> length Ai"
  define Ci where "Ci \<equiv> map C'_of Ai"  
  define Aij where "Aij \<equiv> map Aj_of Ai"
  define CAi where "CAi \<equiv> map CA_of Ai"
    
  have m_nz: "\<And>A. A \<in> set Ai \<Longrightarrow> Aj_of A \<noteq> {#}"
    using prod_c0 unfolding Aj_of_def using produces_imp_Pos_in_lits by (metis (full_types) filter_mset_empty_conv image_mset_is_empty_iff) 
      
  {
    fix CA
    assume "CA \<in> set CAi"
    then obtain i where i_p: "i < length CAi" "CAi ! i = CA"
      by (meson in_set_conv_nth)
    let ?A = "Ai ! i"
    have "production N (CA_of (Ai ! i)) = {Ai ! i}" using i_p CAi_def prod_c0 by auto 
    then have "productive N CA" using i_p CAi_def by auto 
  }
  then have prod_c: "\<And>CA. CA \<in> set CAi \<Longrightarrow> productive N CA" .
  hence cs_subs_n: "set CAi \<subseteq> N"
    using productive_in_N by auto
  have cs_true: "INTERP N \<Turnstile>m mset CAi"
    unfolding true_cls_mset_def using prod_c productive_imp_true_in_INTERP by auto
    
  have "\<And>A. A \<in> set Ai \<Longrightarrow> \<not> Neg A \<in># CA_of A"
    using prod_c0 produces_imp_neg_notin_lits by auto
  hence a_ni_c': "\<And>A. A \<in> set Ai \<Longrightarrow> A \<notin> atms_of (C'_of A)"
    unfolding C'_of_def using atm_imp_pos_or_neg_lit by force
  have c'_le_c: "\<And>A. C'_of A \<le> CA_of A"
    unfolding C'_of_def by (auto intro: subset_eq_imp_le_multiset)
  have a_max_c: "\<And>A. A \<in> set Ai \<Longrightarrow> A = Max (atms_of (CA_of A))"
    using prod_c0 productive_imp_produces_Max_atom[of N] by auto
  hence "\<And>A. A \<in> set Ai \<Longrightarrow> C'_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (C'_of A)) \<le> A"
    using c'_le_c by (metis less_eq_Max_atms_of)
  moreover have "\<And>A. A \<in> set Ai \<Longrightarrow> C'_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (C'_of A)) \<noteq> A"
    using a_ni_c' Max_in by (metis (no_types) atms_empty_iff_empty finite_atms_of)
  ultimately have max_c'_lt_a: "\<And>A. A \<in> set Ai \<Longrightarrow> C'_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (C'_of A)) < A"
    by (metis order.strict_iff_order)
  
  have le_cs_as: "length CAi = length Ai"  unfolding CAi_def by simp     
      
  have "length CAi = n" by (simp add: le_cs_as n_def) 
  moreover
  have "length Ci = n" by (simp add: Ci_def n_def) 
  moreover
  have "length Aij = n" by (simp add: Aij_def n_def) 
  moreover
  have "length Ai = n" using n_def by auto
  moreover
  have "n \<noteq> 0" by (simp add: as_ne n_def) 
  moreover
  have " \<forall>i. i < length Aij \<longrightarrow> (\<forall>A \<in># Aij ! i. A = Ai ! i)"
    using Aij_def Aj_of_def by auto
  have "\<And>x B. production N (CA_of x) = {x} \<Longrightarrow> B \<in># CA_of x \<Longrightarrow> B \<noteq> Pos x \<Longrightarrow> atm_of B < x" 
    by (metis atm_of_lit_in_atms_of insert_not_empty le_imp_less_or_eq Pos_atm_of_iff
          Neg_atm_of_iff pos_neg_in_imp_true produces_imp_Pos_in_lits produces_imp_atms_leq
          productive_imp_false_interp)
  hence "\<And>B A. A\<in>set Ai \<Longrightarrow> B \<in># CA_of A \<Longrightarrow> B \<noteq> Pos A \<Longrightarrow> atm_of B < A" using prod_c0 by auto
  have "\<forall>i. i < length Aij \<longrightarrow> Aij ! i \<noteq> {#}"
    unfolding Aij_def
    using m_nz by simp
  have "\<forall>i<n. CAi ! i = Ci ! i + poss (Aij ! i)"
    unfolding CAi_def Ci_def Aij_def
      using ca_of_c_of_aj_of
      by (simp add: n_def)
  moreover
  have "\<forall>i<n. Aij ! i \<noteq> {#}"
    using \<open>\<forall>i<length Aij. Aij ! i \<noteq> {#}\<close>
    using calculation(3) by blast
  moreover
  have "\<forall>i<n. \<forall>A\<in>#Aij ! i. A = Ai ! i"
    by (simp add: \<open>\<forall>i<length Aij. \<forall>A\<in>#Aij ! i. A = Ai ! i\<close> calculation(3))
  moreover
  have "eligible Ai DAi" using s_d by auto
  hence "eligible Ai (D + negs (mset Ai))" using D_def negs_as_le_d by auto 
  moreover
  have "\<And>i. i < length Aij \<Longrightarrow> str_maximal_in (Ai ! i) ((Ci ! i))"
    by (simp add: C'_of_def Ci_def \<open>\<And>x B. \<lbrakk>production N (CA_of x) = {x}; B \<in># CA_of x; B \<noteq> Pos x\<rbrakk> \<Longrightarrow> atm_of B < x\<close> atms_of_def calculation(3) n_def prod_c0 str_maximal_in_def) 
  have "\<forall>i<n. str_maximal_in (Ai ! i) (Ci ! i)"
    by (simp add: \<open>\<And>i. i < length Aij \<Longrightarrow> str_maximal_in (Ai ! i) (Ci ! i)\<close> calculation(3))
  moreover
  have "\<forall>C \<in> set CAi. S C = {#}"
    using prod_c producesD productive_imp_produces_Max_literal by blast 
  have "\<forall>C\<in>set CAi. S C = {#}"
    using \<open>\<forall>C\<in>set CAi. S C = {#}\<close> by simp
  ultimately
  have res_e: "ord_resolve CAi (D + negs (mset Ai)) (\<Union>#mset Ci + D)" using ord_resolve[of CAi n Ci Aij Ai D] by auto
          
  
  have "\<And>A. A \<in> set Ai \<Longrightarrow> \<not> interp N (CA_of A) \<Turnstile> CA_of A"
    by (simp add: prod_c0 producesD)
  hence "\<And>A. A \<in> set Ai \<Longrightarrow> \<not> Interp N (CA_of A) \<Turnstile> C'_of A"
    unfolding prod_c0 C'_of_def Interp_def true_cls_def 
    using true_lit_def not_gr_zero
    using prod_c0 by auto 
  hence c'_at_n: "\<And>A. A \<in> set Ai \<Longrightarrow> \<not> INTERP N \<Turnstile> C'_of A"
    using a_max_c c'_le_c max_c'_lt_a false_Interp_imp_INTERP unfolding true_cls_def
    by (metis true_cls_def true_cls_empty)
  have "\<not> INTERP N \<Turnstile> \<Union>#mset Ci"
    unfolding Ci_def true_cls_def by (auto dest!: c'_at_n)
  moreover have "\<not> INTERP N \<Turnstile> D"
    using d_cex unfolding main_clause_def
    by (metis D_def add_diff_cancel_right' negs_as_le_d subset_mset.add_diff_assoc2 true_cls_def union_iff) 
  ultimately have e_cex: "\<not> INTERP N \<Turnstile> \<Union>#mset Ci + D"
    by simp
    
  have "set CAi \<subseteq> N"
    by (simp add: cs_subs_n) 
  moreover
  have "INTERP N \<Turnstile>m mset CAi"
    by (simp add: cs_true)
  moreover
  have "\<And>CA. CA \<in> set CAi \<Longrightarrow> productive N CA"
    by (simp add: prod_c) 
  moreover
  have "ord_resolve CAi DAi (\<Union>#mset Ci + D)"
    using D_def negs_as_le_d res_e by auto
  moreover
  have "\<not> INTERP N \<Turnstile> \<Union>#mset Ci + D"
    using e_cex by simp
  moreover
  have "(\<Union>#mset Ci + D) < DAi"
    using calculation(4) ord_resolve_reductive by auto
  ultimately
  show ?thesis ..
  
  (* You can trim a lot in this proof *)
qed

lemma ord_resolve_atms_of_concl_subset:
  assumes res_e: "ord_resolve CAi DAi E"
  shows "atms_of E \<subseteq> (\<Union>C \<in> set CAi. atms_of C) \<union> atms_of DAi"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Ci Aij Ai D)
  have dai: "DAi = D + negs (mset Ai)" using ord_resolve by -
  have e: "E = \<Union>#mset Ci + D" using ord_resolve by -
  have cai: "\<forall>i<n. CAi ! i = Ci ! i + poss (Aij ! i)" using ord_resolve by -
  
  from cai have "\<forall>i<n. set_mset (Ci ! i) \<subseteq> set_mset (CAi ! i)" by auto
  hence "\<forall>i<n. (Ci ! i) \<subseteq># \<Union>#(mset CAi)"
    by (metis cai local.ord_resolve(3) mset_subset_eq_add_left nth_mem_mset sum_mset.remove union_assoc)  
  hence "\<forall>C \<in> set Ci. C \<subseteq># \<Union>#(mset CAi)" using ord_resolve(4) in_set_conv_nth[of _ Ci] by auto
  hence "set_mset (\<Union>#(mset Ci)) \<subseteq> set_mset (\<Union>#(mset CAi))"
    by auto (meson in_mset_sum_list2 mset_subset_eqD) 
  hence "atms_of (\<Union>#mset Ci) \<subseteq> atms_of (\<Union>#mset CAi)" 
    by (meson lits_subseteq_imp_atms_subseteq mset_subset_eqD subsetI)
  moreover    
  have "atms_of (\<Union>#mset CAi) = (\<Union>C\<in>set CAi. atms_of C)"
    apply auto
    apply (metis (no_types, lifting) in_mset_sum_list in_mset_sum_list2 atm_imp_pos_or_neg_lit neg_lit_in_atms_of pos_lit_in_atms_of)+
    done
  ultimately
  have "atms_of (\<Union>#mset Ci) \<subseteq> (\<Union>C\<in>set CAi. atms_of C)" by auto
  moreover
  have "atms_of D \<subseteq> atms_of DAi" using dai by auto
  ultimately
  show ?thesis unfolding e by auto
qed


subsection {* Inference System *}

text {*
Theorem 3.16 is subsumed in the counterexample-reducing inference system framework, which is
instantiated below. Unlike its unordered cousin, ordered resolution is additionally a reductive
inference system.
*}

definition ord_\<Gamma> :: "'a inference set" where
  "ord_\<Gamma> = {Infer (mset CAi) DAi E | CAi DAi E. ord_resolve CAi DAi E}"

sublocale 
  sound_counterex_reducing_inference_system "ground_resolution_with_selection.ord_\<Gamma> S"
    "ground_resolution_with_selection.INTERP S" +
  reductive_inference_system "ground_resolution_with_selection.ord_\<Gamma> S"
proof unfold_locales
  fix DAi :: "'a clause" and N :: "'a clause set"
  thm ord_resolve_counterex_reducing
  assume "{#} \<notin> N" and "DAi \<in> N" and "\<not> INTERP N \<Turnstile> DAi" and "\<And>C. C \<in> N \<Longrightarrow> \<not> INTERP N \<Turnstile> C \<Longrightarrow> DAi \<le> C"
  then obtain CAi E where
    dd_sset_n: "set CAi \<subseteq> N" and
    dd_true: "INTERP N \<Turnstile>m mset CAi" and
    res_e: "ord_resolve CAi DAi E" and
    e_cex: "\<not> INTERP N \<Turnstile> E" and
    e_lt_c: "E < DAi"
    using ord_resolve_counterex_reducing[of N DAi thesis] by auto

  have "ord_resolve CAi DAi E" by (simp add: res_e)
  then have "Infer (mset CAi) DAi E \<in> ord_\<Gamma>"
    unfolding ord_\<Gamma>_def by (metis (mono_tags, lifting) mem_Collect_eq)
  thus "\<exists>CC E. set_mset CC \<subseteq> N \<and> INTERP N \<Turnstile>m CC \<and> Infer CC DAi E \<in> ord_\<Gamma> \<and> \<not> INTERP N \<Turnstile> E \<and> E < DAi"
    using dd_sset_n dd_true e_cex e_lt_c
    by (metis set_mset_mset)
next
  fix CC DAi E and I
  assume inf: "Infer CC DAi E \<in> ord_\<Gamma>" and icc: "I \<Turnstile>m CC" and id: "I \<Turnstile> DAi"
  thm ord_\<Gamma>_def
  from inf obtain mCC where 
    "mset mCC = CC"
    "ord_resolve mCC DAi E" using ord_\<Gamma>_def by auto
  thus "I \<Turnstile> E" using id icc ord_resolve_sound[of mCC DAi E I] by auto
next
  fix \<gamma>
  assume "\<gamma> \<in> ord_\<Gamma>"
  thus "concl_of \<gamma> < main_prem_of \<gamma>"
    unfolding ord_\<Gamma>_def using ord_resolve_reductive by auto
qed

end

text {*
A second proof of Theorem 3.12, compactness of clausal logic:
*}

lemmas (in ground_resolution_with_selection) clausal_logic_compact = clausal_logic_compact


end