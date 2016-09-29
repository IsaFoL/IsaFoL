(*  Title:       Ordered Ground Resolution with Selection
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section {* Ordered Ground Resolution with Selection *}

theory New_Ordered_Ground_Resolution
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

subsection {* Main and side clauses *} (* Should maybe be in Clausal_Logic *)

type_synonym 'a side_clause = "'a clause * 'a multiset"
type_synonym 'a main_clause = "'a clause * 'a list"

abbreviation "side_clause \<equiv> (\<lambda>(C,A). C + {#Pos Atm. Atm \<in># A #})"
abbreviation "main_clause \<equiv> (\<lambda>(D,A). D + {#Neg Atm. Atm \<in># mset A #})"


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
  ord_resolve :: "'a side_clause multiset \<Rightarrow> 'a main_clause \<Rightarrow> 'a clause \<Rightarrow> bool"
where
  ord_resolve:
  "Cf' = \<Union># {#C'. (C', A, m) \<in># ZZ#} \<Longrightarrow>
   AA = {#A. (C', A, m) \<in># ZZ#} \<Longrightarrow>
   AA = mset As \<Longrightarrow>
   image_mset side_clause CC = {#C' + replicate_mset (Suc m) (Pos A). (C', A, m) \<in># ZZ#} \<Longrightarrow>
   ZZ \<noteq> {#} \<Longrightarrow>
   S (main_clause (D,As)) = negs AA \<or> S (main_clause (D,As)) = {#} \<and> size AA = 1 \<and> Max (atms_of (main_clause (D,As))) \<in># AA \<Longrightarrow>
   (\<forall>(C', A, _) \<in> set_mset ZZ. \<forall>B \<in> atms_of C'. B < A) \<Longrightarrow>
   (\<forall>C. C \<in># (image_mset side_clause CC) \<longrightarrow> S C = {#}) \<Longrightarrow>
   ord_resolve CC (D,As) (Cf' + D)"

lemma ord_resolve_sound:
  assumes
    res_e: "ord_resolve CC (D,As) E" and
    cc_true: "I \<Turnstile>m image_mset side_clause CC" and
    d_true: "I \<Turnstile> main_clause (D,As)"
  shows "I \<Turnstile> E"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve Cf' ZZ AA)
  note e = this(1) and cf' = this(2) and aa = this(3) and aa' = this(4) and cc = this(5) and d = this(6)

  show ?thesis
  proof (cases "\<forall>A. A \<in># AA \<longrightarrow> A \<in> I")
    case True
    hence "\<not> I \<Turnstile> negs AA"
      unfolding true_cls_def by fastforce
    hence "I \<Turnstile> D"
      using d_true unfolding d using aa' by fast
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
      aaa: "Am = replicate_mset (Suc m) (Pos A)" by simp
    have c_in_cc: "C' + Am \<in># image_mset side_clause CC" using cam unfolding cc aaa by force
    have "\<not> I \<Turnstile> Am" using aaa a_false by force
    moreover have "I \<Turnstile> C' + Am"
      using c_in_cc cc_true unfolding true_cls_mset_def by blast 
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
  assumes res_e: "ord_resolve CC (D,As) E"
  shows "E < main_clause (D,As)"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve Cf' ZZ AA)
  note e = this(1) and cf' = this(2) and aa = this(3) and aa' = this(4) and zz_ne = this(6) and
    a_max = this(8)

  show ?thesis
  proof (cases "Cf' = {#}")
    case True
    have "negs AA \<noteq> {#}"
      unfolding aa using zz_ne aa by force
    thus ?thesis
      unfolding e aa' True by auto
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
      unfolding e aa' by simp
  qed
qed

theorem range_image_mset:
  assumes "\<forall>D. D \<in># Ds \<longrightarrow> D \<in> range side_clause" 
  shows "Ds \<in> range (image_mset side_clause)"
proof -
  have "\<forall>D. D \<in># Ds \<longrightarrow> (\<exists>C. side_clause C = D)" using assms by blast
  then obtain f where f_p: "\<forall>D. D \<in># Ds \<longrightarrow> (side_clause (f D) = D)" by metis
  define Cs where "Cs \<equiv> image_mset f Ds"
  from f_p Cs_def have "image_mset side_clause Cs = Ds" by auto
  then show ?thesis by blast
qed

text {*
This corresponds to Theorem 3.15:
*}

theorem ord_resolve_counterex_reducing:
  assumes
    ec_ni_n: "{#} \<notin> N" and
    c_in_n: "C \<in> N" and
    c_cex: "\<not> INTERP N \<Turnstile> C" and
    c_min: "\<And>D. D \<in> N \<Longrightarrow> \<not> INTERP N \<Turnstile> D \<Longrightarrow> C \<le> D"
  obtains DD E mC where
    "main_clause mC = C" (* This line was added to fit the new definition. It does not look so nice... *)
    "set_mset (image_mset side_clause DD) \<subseteq> N"
    "INTERP N \<Turnstile>m image_mset side_clause DD"
    "\<And>D. D \<in># image_mset side_clause DD \<Longrightarrow> productive N D"
    "ord_resolve DD mC E"
    "\<not> INTERP N \<Turnstile> E"
    "E < C"
proof -
  have c_ne: "C \<noteq> {#}"
    using c_in_n ec_ni_n by blast
  have "\<exists>AA. AA \<noteq> {#} \<and> negs AA \<le># C \<and>
    (S C = negs AA \<or> S C = {#} \<and> size AA = 1 \<and> Max (atms_of C) \<in># AA)"
  proof (cases "S C = {#}")
    case True
    note s_c_e = this
    hence "\<exists>A. A \<in> atms_of C \<and> A = Max (atms_of C)"
      using c_ne by (blast intro: Max_in_lits atm_of_Max_lit atm_of_lit_in_atms_of)
    hence "\<exists>A. Neg A \<in># C \<and> A = Max (atms_of C)"
      using s_c_e c_ne c_in_n c_cex c_min
      by (metis Max_in_lits Max_lit_eq_pos_or_neg_Max_atm max_pos_imp_true_in_Interp
        true_Interp_imp_INTERP)
    then obtain A where
      "{#A#} \<noteq> {#}" and "{#Neg A#} \<le># C" and "A = Max (atms_of C)"
      by (auto intro: mset_subset_eq_single)
    thus ?thesis
      using s_c_e unfolding One_nat_def
      by (metis (no_types) One_nat_def image_mset_single multi_member_last size_single)
  next
    case False
    then obtain AA where aa_ne: "AA \<noteq> {#}" and aa: "AA = {#atm_of L. L \<in># S C#}"
      by auto
    have "S C = negs AA"
      unfolding aa by (auto simp: filter_neg_atm_of_S)
    moreover have "negs AA \<le># C"
      unfolding aa using S_selects_subseteq by (auto simp: filter_neg_atm_of_S)
    ultimately show ?thesis
      using aa_ne by auto
  qed
  then obtain AA where
    aa_ne: "AA \<noteq> {#}" and
    negs_aa_le_c: "negs AA \<le># C" and
    s_c: "S C = negs AA \<or> S C = {#} \<and> size AA = 1 \<and> Max (atms_of C) \<in># AA"
    by blast
  obtain C' where c: "C = negs AA + C'"
    using negs_aa_le_c mset_subset_eq_exists_conv by blast
  define As where "As \<equiv> sorted_list_of_multiset AA"
  have asaa: "AA = mset As" using As_def by auto
  have c'asc: "main_clause (C',As) = C" by (simp add: asaa c union_commute)
  from s_c c'asc have s_mc: "S (main_clause (C',As)) = negs AA \<or> S (main_clause (C',As)) = {#} \<and> size AA = 1 \<and> Max (atms_of (main_clause (C',As))) \<in># AA" by auto
  from negs_aa_le_c have neg_a_in_c: "\<And>A. A \<in># AA \<Longrightarrow> Neg A \<in># C"
    by fastforce
  have "\<And>A. A \<in># AA \<Longrightarrow> A \<in> INTERP N"
    using c_cex neg_a_in_c by force
  hence prod_ex: "\<And>A. A \<in># AA \<Longrightarrow> \<exists>D. produces N D A"
    unfolding INTERP_def by (metis UN_E not_produces_imp_notin_production)
  hence "\<And>A. \<exists>D. produces N D A \<longrightarrow> A \<in># AA"
    using ec_ni_n by (auto intro: productive_in_N)
  hence "\<And>A. \<exists>D. produces N D A \<longleftrightarrow> A \<in># AA"
    using prod_ex by blast
  then obtain D_of where d_of0: "\<And>A. produces N (D_of A) A \<longleftrightarrow> A \<in># AA"
    by metis
  hence prod_d0: "\<And>A. A \<in># AA \<Longrightarrow> produces N (D_of A) A"
    by blast

  define D'_of where "D'_of \<equiv> \<lambda>A. {#L \<in># D_of A. L \<noteq> Pos A#}"
  define M_of where "M_of \<equiv> \<lambda>A. count (D_of A) (Pos A)"

  have d_of: "D_of = (\<lambda>A. D'_of A + replicate_mset (M_of A) (Pos A))"
    unfolding D'_of_def M_of_def
    by (rule ext) (metis add.commute filter_eq_replicate_mset multiset_partition)
  have m_nz: "\<And>A. A \<in># AA \<Longrightarrow> M_of A \<noteq> 0"
    using prod_d0 unfolding M_of_def by (auto intro: produces_imp_Pos_in_lits)

  define ZZ where "ZZ \<equiv> {#(D'_of A, A, M_of A - 1). A \<in># AA#}"
  define Df' where "Df' \<equiv> \<Union># {#D'. (D', A, m) \<in># ZZ#}"
  define Df where "Df \<equiv> Df' + negs AA"
  define DD where "DD \<equiv> inv (image_mset side_clause) {#D' + replicate_mset (Suc m) (Pos A). (D', A, m) \<in># ZZ#}"
  have DD_def: "image_mset side_clause DD \<equiv> {#D' + replicate_mset (Suc m) (Pos A). (D', A, m) \<in># ZZ#}"
  proof -
    have "\<forall>C. C = side_clause (C,{#})" by auto
    then have "range side_clause = UNIV" by blast
    then have "\<forall>D. D \<in># ({#D' + replicate_mset (Suc m) (Pos A). (D', A, m) \<in># ZZ#}) \<longrightarrow> D \<in> range side_clause"
      by auto
    then have in_range: "{#D' + replicate_mset (Suc m) (Pos A). (D', A, m) \<in># ZZ#} \<in> range (image_mset side_clause)"
      using range_image_mset by blast
      
    
    have "DD = inv (image_mset side_clause) {#D' + replicate_mset (Suc m) (Pos A). (D', A, m) \<in># ZZ#}" using DD_def by auto
    then have "image_mset side_clause DD = image_mset side_clause (inv (image_mset side_clause) {#D' + replicate_mset (Suc m) (Pos A). (D', A, m) \<in># ZZ#})" by auto
    then show "image_mset side_clause DD \<equiv> {#D' + replicate_mset (Suc m) (Pos A). (D', A, m) \<in># ZZ#}"
      using f_inv_into_f[of "{#D' + replicate_mset (Suc m) (Pos A). (D', A, m) \<in># ZZ#}" "image_mset side_clause" UNIV]
      using in_range by auto
  qed

  have df': "Df' = \<Union># {#D'_of A. A \<in># AA#}"
    unfolding Df'_def ZZ_def by auto
  have dd: "image_mset side_clause DD = {#D_of A. A \<in># AA#}"
    unfolding DD_def ZZ_def d_of
    apply simp 
    apply (rule image_mset_cong, metis Suc_pred m_nz neq0_conv replicate_mset_Suc
        union_mset_add_mset_right)
    done
  have prod_d: "\<And>D. D \<in># image_mset side_clause DD \<Longrightarrow> productive N D"
    unfolding dd by (auto dest!: prod_d0)
  hence dd_subs_n: "set_mset (image_mset side_clause DD) \<subseteq> N"
    using productive_in_N by auto
  have dd_true: "INTERP N \<Turnstile>m (image_mset side_clause DD)"
    unfolding true_cls_mset_def using prod_d productive_imp_true_in_INTERP by blast 
  have s_dd_e: "\<And>D. D \<in># (image_mset side_clause DD) \<Longrightarrow> S D = {#}"
    using prod_d in_production_imp_produces producesD
    by (meson productive_imp_produces_Max_literal) 

  have "Df' = \<Union># {#C'. (C', A, m) \<in># ZZ#}"
    unfolding Df'_def DD_def
    by simp 
  moreover have "AA = {#A. (C', A, m) \<in># ZZ#}"
    unfolding ZZ_def by simp
  moreover have "image_mset side_clause DD = {#C' + replicate_mset (Suc m) (Pos A). (C', A, m) \<in># ZZ#}"
    unfolding DD_def ZZ_def Df'_def by simp
  moreover have "ZZ \<noteq> {#}"
    unfolding ZZ_def using aa_ne by simp
  moreover have "\<forall>(C', A, m) \<in> set_mset ZZ. \<forall>B \<in> atms_of C'. B < A"
     by (auto simp: ZZ_def D'_of_def atms_of_def intro: produces_imp_Max_atom dest!: prod_d0)
       (metis atm_of_lit_in_atms_of insert_not_empty le_imp_less_or_eq Pos_atm_of_iff
          Neg_atm_of_iff pos_neg_in_imp_true produces_imp_Pos_in_lits produces_imp_atms_leq
          productive_imp_false_interp)
  moreover have "\<forall>C. C \<in># image_mset side_clause DD \<longrightarrow> S C = {#}" using s_dd_e by auto
  moreover have "\<not> interp N C \<Turnstile> C"
    by (metis c_cex c_in_n c_min true_interp_imp_INTERP)
  ultimately have res_e: "ord_resolve DD (C', As) (Df' + C')"
    using c s_mc s_dd_e asaa ord_resolve.intros[of Df' ZZ AA As DD C'] by blast

  have "\<And>A. A \<in># AA \<Longrightarrow> \<not> Neg A \<in># D_of A"
    by (drule prod_d0) (auto dest: produces_imp_neg_notin_lits)
  hence a_ni_d': "\<And>A. A \<in># AA \<Longrightarrow> A \<notin> atms_of (D'_of A)"
    unfolding D'_of_def using atm_imp_pos_or_neg_lit by force
  have d'_le_d: "\<And>A. D'_of A \<le> D_of A"
    unfolding D'_of_def by (auto intro: subset_eq_imp_le_multiset)
  have a_max_d: "\<And>A. A \<in># AA \<Longrightarrow> A = Max (atms_of (D_of A))"
    using prod_d0 productive_imp_produces_Max_atom[of N] by auto
  hence "\<And>A. A \<in># AA \<Longrightarrow> D'_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (D'_of A)) \<le> A"
    using d'_le_d by (metis less_eq_Max_atms_of)
  moreover have "\<And>A. A \<in># AA \<Longrightarrow> D'_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (D'_of A)) \<noteq> A"
    using a_ni_d' Max_in by (metis (no_types) atms_empty_iff_empty finite_atms_of)
  ultimately have max_d'_lt_a: "\<And>A. A \<in># AA \<Longrightarrow> D'_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (D'_of A)) < A"
    by (metis order.strict_iff_order)

  have "\<And>D. D \<in># image_mset side_clause DD \<Longrightarrow> \<not> interp N D \<Turnstile> D"
    using prod_d productive_imp_false_interp by blast
  hence "\<And>A. A \<in># AA \<Longrightarrow> \<not> interp N (D_of A) \<Turnstile> D_of A"
    unfolding dd by auto 
  hence "\<And>A. A \<in># AA \<Longrightarrow> \<not> Interp N (D_of A) \<Turnstile> D'_of A"
    unfolding prod_d0 D'_of_def Interp_def true_cls_def 
    by (auto simp: true_lit_def simp del: not_gr_zero)
  hence d'_at_n: "\<And>A. A \<in># AA \<Longrightarrow> \<not> INTERP N \<Turnstile> D'_of A"
    using a_max_d d'_le_d max_d'_lt_a false_Interp_imp_INTERP unfolding true_cls_def
    by (metis true_cls_def true_cls_empty)
  have "\<not> INTERP N \<Turnstile> Df'"
    unfolding df' true_cls_def by (auto dest!: d'_at_n)
  moreover have "\<not> INTERP N \<Turnstile> C'"
    using c_cex unfolding c by simp
  ultimately have e_cex: "\<not> INTERP N \<Turnstile> Df' + C'"
    by simp

  have "Df' + C' < main_clause (C', As)" using res_e ord_resolve_reductive by simp

  then have lt_cex: "Df' + C' < C" by (simp add: asaa c union_commute) 
 
  from c'asc dd_subs_n dd_true prod_d res_e e_cex lt_cex show ?thesis .. 
qed

lemma ord_resolve_atms_of_concl_subset:
  assumes res_e: "ord_resolve CC (D,As) E"
  shows "atms_of E \<subseteq> (\<Union>C \<in> set_mset (image_mset side_clause CC). atms_of C) \<union> atms_of (main_clause (D,As))"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve Cf' ZZ AA)
  note e = this(1) and cf' = this(2) and cc = this(5) and d = this(4)
  thm d
  have "atms_of Cf' \<subseteq> (\<Union>C\<in>set_mset (image_mset side_clause CC). atms_of C)"
    unfolding cf' cc by (auto simp: atms_of_def)
  moreover have "atms_of D \<subseteq> atms_of (main_clause (D,As))"
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
  "ord_\<Gamma> = {Infer (image_mset side_clause CC) (main_clause (D,As)) E | CC D As E. ord_resolve CC (D,As) E}"

sublocale 
  sound_counterex_reducing_inference_system "ground_resolution_with_selection.ord_\<Gamma> S"
    "ground_resolution_with_selection.INTERP S" +
  reductive_inference_system "ground_resolution_with_selection.ord_\<Gamma> S"
proof unfold_locales
  fix C :: "'a clause" and N :: "'a clause set"
  thm ord_resolve_counterex_reducing
  assume "{#} \<notin> N" and "C \<in> N" and "\<not> INTERP N \<Turnstile> C" and "\<And>D. D \<in> N \<Longrightarrow> \<not> INTERP N \<Turnstile> D \<Longrightarrow> C \<le> D"
  then obtain DD E mC where
    mc: "main_clause mC = C" and
    dd_sset_n: "set_mset (image_mset side_clause DD) \<subseteq> N" and
    dd_true: "INTERP N \<Turnstile>m image_mset side_clause DD" and
    res_e: "ord_resolve DD mC E" and
    e_cex: "\<not> INTERP N \<Turnstile> E" and
    e_lt_c: "E < C"
    using ord_resolve_counterex_reducing[of N C thesis] by auto

  have mc': "main_clause (fst mC, snd mC) = C" by (simp add: mc)

  have "ord_resolve DD mC E" by (simp add: res_e)
  then have "ord_resolve DD (fst mC, snd mC) E" by simp
  then have "Infer (image_mset side_clause DD) C E \<in> ord_\<Gamma>"
    using mc mc' unfolding ord_\<Gamma>_def by (metis (mono_tags, lifting) mem_Collect_eq)
  thus "\<exists>DD E. set_mset DD \<subseteq> N \<and> INTERP N \<Turnstile>m DD \<and> Infer DD C E \<in> ord_\<Gamma> \<and> \<not> INTERP N \<Turnstile> E \<and> E < C"
    using dd_sset_n dd_true e_cex e_lt_c by blast
next
  fix CC DAs E and I
  assume inf: "Infer CC DAs E \<in> ord_\<Gamma>" and icc: "I \<Turnstile>m CC" and id: "I \<Turnstile> DAs"
  thm ord_\<Gamma>_def
  from inf obtain D As mCC where "image_mset side_clause mCC = CC" "main_clause (D,As) = DAs" "ord_resolve mCC (D, As) E" using ord_\<Gamma>_def by auto
  thus "I \<Turnstile> E" using id icc ord_resolve_sound[of mCC D As E I] by auto
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
