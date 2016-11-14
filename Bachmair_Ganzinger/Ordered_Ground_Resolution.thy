(*  Title:       Ordered Ground Resolution with Selection
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section {* Ordered Ground Resolution with Selection *}

theory Ordered_Ground_Resolution
imports Inference_System Ground_Resolution_Model
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

inductive
  ord_resolve :: "'a clause multiset \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool"
where
  ord_resolve:
  "Cf' = \<Union># {#C'. (C', A, m) \<in># ZZ#} \<Longrightarrow>
   AA = {#A. (C', A, m) \<in># ZZ#} \<Longrightarrow>
   CC = {#C' + replicate_mset (Suc m) (Pos A). (C', A, m) \<in># ZZ#} \<Longrightarrow>
   D = negs AA + D' \<Longrightarrow>
   ZZ \<noteq> {#} \<Longrightarrow>
   S D = negs AA \<or> S D = {#} \<and> size AA = 1 \<and> Max (atms_of D) \<in># AA \<Longrightarrow>
   (\<forall>(C', A, _) \<in> set_mset ZZ. \<forall>B \<in> atms_of C'. B < A) \<Longrightarrow>
   (\<forall>C. C \<in># CC \<longrightarrow> S C = {#}) \<Longrightarrow>
   ord_resolve CC D (Cf' + D')"

lemma ord_resolve_sound:
  assumes
    res_e: "ord_resolve CC D E" and
    cc_true: "I \<Turnstile>m CC" and
    d_true: "I \<Turnstile> D"
  shows "I \<Turnstile> E"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve Cf' ZZ AA D')
  have e: "E = Cf' + D'" using ord_resolve(1) .
  have cf': "Cf' = \<Union>#{#C'. (C', A, m) \<in># ZZ#}" using ord_resolve(2) .
  have aa: "AA = {#A. (C', A, m) \<in># ZZ#}" using ord_resolve(3) .
  have cc: "CC = {#C' + replicate_mset (Suc m) (Pos A). (C', A, m) \<in># ZZ#}" using ord_resolve(4) .
  have d: "D = negs AA + D'" using ord_resolve(5) .
  
  show ?thesis
  proof (cases "\<forall>A. A \<in># AA \<longrightarrow> A \<in> I")
    case True
    hence "\<not> I \<Turnstile> negs AA"
      unfolding true_cls_def by fastforce
    hence "I \<Turnstile> D'"
      using d_true unfolding d by fast
    thus ?thesis
      unfolding e by blast
  next
    case False
    then obtain A where a_in_aa: "A \<in># AA" and a_false: "A \<notin> I"
      by blast
    from a_in_aa obtain C' m where cam: "(C', A, m) \<in># ZZ"
      unfolding aa by auto
    hence c_cf': "set_mset C' \<subseteq> set_mset Cf'"
      unfolding cf' by force
    obtain Am where
      aaa: "Am = replicate_mset (Suc m) (Pos A)" and c_in_cc: "C' + Am \<in># CC"
      using cam unfolding cc by force
    have "\<not> I \<Turnstile> Am"
      using aaa a_false by simp
    moreover have "I \<Turnstile> C' + Am"
      using c_in_cc cc_true unfolding true_cls_mset_def by auto
    ultimately have "I \<Turnstile> C'"
      by simp
    thus ?thesis
      unfolding e using c_cf' by (blast intro: true_cls_mono)
  qed
qed

lemma filter_neg_atm_of_S: "{#Neg (atm_of L). L \<in># S C#} = S C"
  by (rule trans[OF image_mset_cong[of "S C" "\<lambda>L. Neg (atm_of L)" id]])
    (auto intro!: S_selects_neg_lits)

lemma atm_in_ZZ_imp_ex_clause:
  "B \<in> atms_of (\<Union># {#C'. (C', A, m) \<in># ZZ#}) \<Longrightarrow> \<exists>(C, _, _) \<in> set_mset ZZ. B \<in> atms_of C"
  by (induct ZZ) auto

text {*
This corresponds to Lemma 3.13:
*}

lemma ord_resolve_reductive:
  assumes res_e: "ord_resolve CC D E"
  shows "E < D"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve Cf' ZZ AA D')
  have e: "E = Cf' + D'" using ord_resolve(1).
  have cf': "Cf' = \<Union>#{#C'. (C', A, m) \<in># ZZ#}" using ord_resolve(2).
  have aa: "AA = {#A. (C', A, m) \<in># ZZ#}" using ord_resolve(3).
  have d: "D = negs AA + D'" using ord_resolve(5) .
  have zz_ne: "ZZ \<noteq> {#}" using ord_resolve(6) .
  have a_max: "\<forall>(C', A, _)\<in>#ZZ. \<forall>B\<in>atms_of C'. B < A" using ord_resolve (8) .
  
  show ?thesis
  proof (cases "Cf' = {#}")
    case True
    have "negs AA \<noteq> {#}"
      unfolding aa using zz_ne by auto
    thus ?thesis
      unfolding e d True by auto
  next
    case False
    then obtain max_C where
      mc_in: "max_C \<in> atms_of Cf'" and mc_max: "\<And>B. B \<in> atms_of Cf' \<Longrightarrow> B \<le> max_C"
      using finite_atms_of
      by (metis Max_ge Max_in_lits atm_of_Max_lit atm_of_lit_in_atms_of)
    have "AA \<noteq> {#}"
      unfolding aa using zz_ne by auto

    have "\<exists>(C', A, m) \<in> set_mset ZZ. max_C \<in> atms_of C'"
      using mc_in unfolding cf' by (rule atm_in_ZZ_imp_ex_clause)
    then obtain C_max max_A m_max where
      cam: "(C_max, max_A, m_max) \<in># ZZ" and mc_in_cm: "max_C \<in> atms_of C_max"
      unfolding aa by auto
    have ma_in: "max_A \<in># AA"
      unfolding aa using cam by force
    have mc_lt_ma: "max_C < max_A"
      using a_max cam mc_in_cm by auto
    have ma_in': "max_A \<in> atms_of (negs AA)"
      using ma_in by simp
    hence cf'_ne_neg_aa: "Cf' \<noteq> negs AA"
      using mc_in mc_max ma_in mc_lt_ma by (blast dest: leD)

    have cf'_lt_ma: "\<And>B. B \<in> atms_of Cf' \<Longrightarrow> B < max_A"
      using mc_max mc_lt_ma by fastforce
    moreover have "\<not> Neg max_A \<in># Cf'"
      using cf'_lt_ma by (fastforce intro: neg_lit_in_atms_of)
    moreover have "Neg max_A \<in># negs AA"
      using ma_in mc_lt_ma by simp
    ultimately have "Cf' < negs AA"
      using cf'_lt_ma unfolding less_multiset\<^sub>H\<^sub>O
      (* TODO tune proof *)
      by (auto simp: cf'_ne_neg_aa not_in_iff intro!: exI[of _ "Neg max_A"])
        (metis atms_less_eq_imp_lit_less_eq_neg count_inI dual_order.strict_implies_order 
          gr_implies_not_zero order.not_eq_order_implies_strict)
    thus ?thesis
      unfolding e d by simp
  qed
qed

text {*
This corresponds to Theorem 3.15:
*}

theorem ord_resolve_counterex_reducing:
  assumes
    ec_ni_n: "{#} \<notin> N" and
    d_in_n: "D \<in> N" and
    d_cex: "\<not> INTERP N \<Turnstile> D" and
    d_min: "\<And>C. C \<in> N \<Longrightarrow> \<not> INTERP N \<Turnstile> C \<Longrightarrow> D \<le> C"
  obtains CC E where
    "set_mset CC \<subseteq> N"
    "INTERP N \<Turnstile>m CC"
    "\<And>C. C \<in># CC \<Longrightarrow> productive N C"
    "ord_resolve CC D E"
    "\<not> INTERP N \<Turnstile> E"
    "E < D"
proof -
  have d_ne: "D \<noteq> {#}"
    using d_in_n ec_ni_n by blast
  have "\<exists>AA. AA \<noteq> {#} \<and> negs AA \<le># D \<and>
    (S D = negs AA \<or> S D = {#} \<and> size AA = 1 \<and> Max (atms_of D) \<in># AA)"
  proof (cases "S D = {#}")
    case True
    note s_d_e = this
    hence "\<exists>A. A \<in> atms_of D \<and> A = Max (atms_of D)"
      using d_ne by (blast intro: Max_in_lits atm_of_Max_lit atm_of_lit_in_atms_of)
    hence "\<exists>A. Neg A \<in># D \<and> A = Max (atms_of D)"
      using s_d_e d_ne d_in_n d_cex d_min
      by (metis Max_in_lits Max_lit_eq_pos_or_neg_Max_atm max_pos_imp_true_in_Interp
        true_Interp_imp_INTERP)
    then obtain A where
      "{#A#} \<noteq> {#}" and "{#Neg A#} \<le># D" and "A = Max (atms_of D)"
      by (auto intro: mset_subset_eq_single)
    thus ?thesis
      using s_d_e unfolding One_nat_def
      by (metis (no_types) One_nat_def image_mset_single multi_member_last size_single)
  next
    case False
    then obtain AA where aa_ne: "AA \<noteq> {#}" and aa: "AA = {#atm_of L. L \<in># S D#}"
      by auto
    have "S D = negs AA"
      unfolding aa by (auto simp: filter_neg_atm_of_S)
    moreover have "negs AA \<le># D"
      unfolding aa using S_selects_subseteq by (auto simp: filter_neg_atm_of_S)
    ultimately show ?thesis
      using aa_ne by auto
  qed
  then obtain AA where
    aa_ne: "AA \<noteq> {#}" and
    negs_aa_le_d: "negs AA \<le># D" and
    s_d: "S D = negs AA \<or> S D = {#} \<and> size AA = 1 \<and> Max (atms_of D) \<in># AA"
    by blast
  obtain C' where c: "D = negs AA + C'"
    using negs_aa_le_d mset_subset_eq_exists_conv by blast
  from negs_aa_le_d have neg_a_in_d: "\<And>A. A \<in># AA \<Longrightarrow> Neg A \<in># D"
    by fastforce
  have "\<And>A. A \<in># AA \<Longrightarrow> A \<in> INTERP N"
    using d_cex neg_a_in_d by force
  hence prod_ex: "\<And>A. A \<in># AA \<Longrightarrow> \<exists>D. produces N D A"
    unfolding INTERP_def by (metis UN_E not_produces_imp_notin_production)
  hence "\<And>A. \<exists>D. produces N D A \<longrightarrow> A \<in># AA"
    using ec_ni_n by (auto intro: productive_in_N)
  hence "\<And>A. \<exists>D. produces N D A \<longleftrightarrow> A \<in># AA"
    using prod_ex by blast
  (* D_of was renamed to C_of... I don't know if it was a good idea *)
  then obtain C_of where c_of0: "\<And>A. produces N (C_of A) A \<longleftrightarrow> A \<in># AA"
    by metis
  hence prod_c0: "\<And>A. A \<in># AA \<Longrightarrow> produces N (C_of A) A"
    by blast

  def c'_of: C'_of \<equiv> "\<lambda>A. {#L \<in># C_of A. L \<noteq> Pos A#}"
  def m_of: M_of \<equiv> "\<lambda>A. count (C_of A) (Pos A)"

  have d_of: "C_of = (\<lambda>A. C'_of A + replicate_mset (M_of A) (Pos A))"
    unfolding c'_of m_of
    by (rule ext) (metis add.commute filter_eq_replicate_mset multiset_partition)
  have m_nz: "\<And>A. A \<in># AA \<Longrightarrow> M_of A \<noteq> 0"
    using prod_c0 unfolding m_of by (auto intro: produces_imp_Pos_in_lits)

  def zz: ZZ \<equiv> "{#(C'_of A, A, M_of A - 1). A \<in># AA#}"
  def cf'_zz: Cf' \<equiv> "\<Union># {#C'. (C', A, m) \<in># ZZ#}"
  def cf: Cf \<equiv> "Cf' + negs AA"
  def cc_zz: CC \<equiv> "{#C' + replicate_mset (Suc m) (Pos A). (C', A, m) \<in># ZZ#}"

  have cf': "Cf' = \<Union># {#C'_of A. A \<in># AA#}"
    unfolding cf'_zz zz by auto
  have cc: "CC = {#C_of A. A \<in># AA#}"
    unfolding cc_zz zz d_of
    by simp (rule image_mset_cong, 
        metis Suc_pred m_nz neq0_conv replicate_mset_Suc union_mset_add_mset_right)
  have prod_c: "\<And>C. C \<in># CC \<Longrightarrow> productive N C"
    unfolding cc by (auto dest!: prod_c0)
  hence cc_subs_n: "set_mset CC \<subseteq> N"
    using productive_in_N by auto
  have cc_true: "INTERP N \<Turnstile>m CC"
    unfolding true_cls_mset_def using prod_c productive_imp_true_in_INTERP by blast 
  have s_cc_e: "\<And>C. C \<in># CC \<Longrightarrow> S C = {#}"
    by (blast dest: prod_c in_production_imp_produces producesD)

  have "Cf' = \<Union># {#C'. (C', A, m) \<in># ZZ#}"
    unfolding cf'_zz cc_zz ..
  moreover have "AA = {#A. (C', A, m) \<in># ZZ#}"
    unfolding zz by simp
  moreover have "CC = {#C' + replicate_mset (Suc m) (Pos A). (C', A, m) \<in># ZZ#}"
    unfolding cc_zz zz c'_of by simp
  moreover have "ZZ \<noteq> {#}"
    unfolding zz using aa_ne by simp
  moreover have "\<forall>(C', A, m) \<in> set_mset ZZ. \<forall>B \<in> atms_of C'. B < A"
     by (auto simp: zz c'_of atms_of_def intro: produces_imp_Max_atom dest!: prod_c0)
       (metis atm_of_lit_in_atms_of insert_not_empty le_imp_less_or_eq Pos_atm_of_iff
          Neg_atm_of_iff pos_neg_in_imp_true produces_imp_Pos_in_lits produces_imp_atms_leq
          productive_imp_false_interp)
  moreover have "\<not> interp N D \<Turnstile> D"
    by (metis d_cex d_in_n d_min true_interp_imp_INTERP)
  ultimately have res_e: "ord_resolve CC D (Cf' + C')"
    using c s_d s_cc_e using ord_resolve.intros[of Cf' ZZ AA CC D C'] by blast

  have "\<And>A. A \<in># AA \<Longrightarrow> \<not> Neg A \<in># C_of A"
    by (drule prod_c0) (auto dest: produces_imp_neg_notin_lits)
  hence a_ni_c': "\<And>A. A \<in># AA \<Longrightarrow> A \<notin> atms_of (C'_of A)"
    unfolding c'_of using atm_imp_pos_or_neg_lit by force
  have c'_le_c: "\<And>A. C'_of A \<le> C_of A"
    unfolding c'_of by (auto intro: subset_eq_imp_le_multiset)
  have a_max_c: "\<And>A. A \<in># AA \<Longrightarrow> A = Max (atms_of (C_of A))"
    using prod_c0 productive_imp_produces_Max_atom[of N] by auto
  hence "\<And>A. A \<in># AA \<Longrightarrow> C'_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (C'_of A)) \<le> A"
    using c'_le_c by (metis less_eq_Max_atms_of)
  moreover have "\<And>A. A \<in># AA \<Longrightarrow> C'_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (C'_of A)) \<noteq> A"
    using a_ni_c' Max_in by (metis (no_types) atms_empty_iff_empty finite_atms_of)
  ultimately have max_c'_lt_a: "\<And>A. A \<in># AA \<Longrightarrow> C'_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (C'_of A)) < A"
    by (metis order.strict_iff_order)

  have "\<And>C. C \<in># CC \<Longrightarrow> \<not> interp N C \<Turnstile> C"
    using prod_c productive_imp_false_interp by blast
  hence "\<And>A. A \<in># AA \<Longrightarrow> \<not> interp N (C_of A) \<Turnstile> C_of A"
    unfolding cc by auto 
  hence "\<And>A. A \<in># AA \<Longrightarrow> \<not> Interp N (C_of A) \<Turnstile> C'_of A"
    unfolding prod_c0 c'_of Interp_def true_cls_def 
    by (auto simp: true_lit_def simp del: not_gr_zero)
  hence c'_at_n: "\<And>A. A \<in># AA \<Longrightarrow> \<not> INTERP N \<Turnstile> C'_of A"
    using a_max_c c'_le_c max_c'_lt_a false_Interp_imp_INTERP unfolding true_cls_def
    by (metis true_cls_def true_cls_empty)
  have "\<not> INTERP N \<Turnstile> Cf'"
    unfolding cf' true_cls_def by (auto dest!: c'_at_n)
  moreover have "\<not> INTERP N \<Turnstile> C'"
    using d_cex unfolding c by simp
  ultimately have e_cex: "\<not> INTERP N \<Turnstile> Cf' + C'"
    by simp

  have lt_cex: "Cf' + C' < D"
    using res_e ord_resolve_reductive by blast

  from cc_subs_n cc_true prod_c res_e e_cex lt_cex show ?thesis ..
qed

lemma ord_resolve_atms_of_concl_subset:
  assumes res_e: "ord_resolve CC D E"
  shows "atms_of E \<subseteq> (\<Union>C \<in> set_mset CC. atms_of C) \<union> atms_of D"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve Cf' ZZ AA D')
  have e: "E = Cf' + D'" using ord_resolve(1) .
  have cf': "Cf' = \<Union>#{#C'. (C', A, m) \<in># ZZ#}" using ord_resolve(2) .
  have cc: "CC = {#C' + replicate_mset (Suc m) (Pos A). (C', A, m) \<in># ZZ#}" using ord_resolve(4) .
  have d: "D = negs AA + D'" using ord_resolve(5) .

  have "atms_of Cf' \<subseteq> (\<Union>C\<in>set_mset CC. atms_of C)"
    unfolding cf' cc by (auto simp: atms_of_def)
  moreover have "atms_of D' \<subseteq> atms_of D"
    unfolding d by simp
  ultimately show ?thesis
    unfolding e by auto
qed


subsection {* Inference System *}

text {*
Theorem 3.16 is subsumed in the counterexample-reducing inference system framework, which is
instantiated below. Unlike its unordered cousin, ordered resolution is additionally a reductive
inference system.
*}

definition ord_\<Gamma> :: "'a inference set" where
  "ord_\<Gamma> = {Infer CC D E | CC D E. ord_resolve CC D E}"

sublocale 
  sound_counterex_reducing_inference_system "ground_resolution_with_selection.ord_\<Gamma> S"
    "ground_resolution_with_selection.INTERP S" +
  reductive_inference_system "ground_resolution_with_selection.ord_\<Gamma> S"
proof unfold_locales
  fix C :: "'a clause" and N :: "'a clause set"
  assume "{#} \<notin> N" and "C \<in> N" and "\<not> INTERP N \<Turnstile> C" and "\<And>D. D \<in> N \<Longrightarrow> \<not> INTERP N \<Turnstile> D \<Longrightarrow> C \<le> D"
  then obtain DD E where
    dd_sset_n: "set_mset DD \<subseteq> N" and
    dd_true: "INTERP N \<Turnstile>m DD" and
    res_e: "ord_resolve DD C E" and
    e_cex: "\<not> INTERP N \<Turnstile> E" and
    e_lt_c: "E < C"
    using ord_resolve_counterex_reducing by metis
  from res_e have "Infer DD C E \<in> ord_\<Gamma>"
    unfolding ord_\<Gamma>_def by blast
  thus "\<exists>DD E. set_mset DD \<subseteq> N \<and> INTERP N \<Turnstile>m DD \<and> Infer DD C E \<in> ord_\<Gamma> \<and> \<not> INTERP N \<Turnstile> E \<and> E < C"
    using dd_sset_n dd_true e_cex e_lt_c by blast
next
  fix CC D E and I
  assume "Infer CC D E \<in> ord_\<Gamma>" and "I \<Turnstile>m CC" and "I \<Turnstile> D"
  thus "I \<Turnstile> E" using ord_\<Gamma>_def ord_resolve_sound by auto
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
