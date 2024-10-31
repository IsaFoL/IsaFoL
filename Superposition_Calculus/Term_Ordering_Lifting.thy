theory Term_Ordering_Lifting
  imports Clausal_Calculus_Extra Min_Max_Least_Greatest_Multiset
begin

locale strict_order = 
  fixes
    R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes
    transp [intro]: "transp (\<prec>)" and
    asymp [intro]: "asymp (\<prec>)"
begin
 
sublocale order "(\<prec>)\<^sup>=\<^sup>=" "(\<prec>)"
  by(rule order_reflclp_if_transp_and_asymp[OF transp asymp])

end

locale wellfounded_strict_order = strict_order +
  assumes wfp [intro]: "wfp (\<prec>)"
begin

lemma wfp_on [intro]: "\<And>X. wfp_on X (\<prec>)"
  using wfp_on_subset by auto

end

locale total_on_strict_order = strict_order +
  fixes X
  assumes totalp_on [intro]: "totalp_on X (\<prec>)"

locale total_strict_order = total_on_strict_order where X = UNIV
begin

sublocale linorder "(\<prec>)\<^sup>=\<^sup>=" "(\<prec>)"
  using totalpD
  by unfold_locales fastforce

end

locale multiset_extension = base: strict_order +
  fixes to_mset :: "'b \<Rightarrow> 'a multiset"
begin

definition multiset_extension :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<prec>\<^sub>m" 50) where
  "multiset_extension b1 b2 \<equiv> multp (\<prec>) (to_mset b1) (to_mset b2)"

sublocale strict_order "(\<prec>\<^sub>m)"
proof unfold_locales
  show "\<And>X. transp_on X (\<prec>\<^sub>m)"
    using transp_multp[OF base.transp]
    unfolding multiset_extension_def transp_on_def
    by blast
next
  show "\<And>X. asymp_on X (\<prec>\<^sub>m)"
    unfolding multiset_extension_def
    by (simp add: asympD asymp_multp\<^sub>H\<^sub>O asymp_onI multp_eq_multp\<^sub>H\<^sub>O)
qed

end

(* TODO: Investigate restricted wfp *)
locale wellfounded_multiset_extension = 
  base: wellfounded_strict_order + multiset_extension
begin

sublocale wellfounded_strict_order "(\<prec>\<^sub>m)"
proof unfold_locales
  show "\<And>X. wfp_on X (\<prec>\<^sub>m)"
    unfolding multiset_extension_def
    using wfp_multp
    by (metis (no_types, lifting) base.wfp top_greatest wfp_if_convertible_to_wfp wfp_on_subset)
qed

end


locale total_on_multiset_extension = 
  base: total_on_strict_order + multiset_extension +
  assumes inj_on_to_mset: "inj_on to_mset {b. set_mset (to_mset b) \<subseteq> X}"
begin

sublocale total_on_strict_order "(\<prec>\<^sub>m)" "{b. set_mset (to_mset b) \<subseteq> X}"
proof unfold_locales
  have "totalp_on {b. set_mset b \<subseteq> X} (multp (\<prec>))"
    using totalp_on_multp[OF base.totalp_on base.transp]
    by fastforce

  then show "totalp_on {b. set_mset (to_mset b) \<subseteq> X} (\<prec>\<^sub>m)"
    using inj_on_to_mset
    unfolding multiset_extension_def totalp_on_def inj_on_def
    by auto
qed

end

locale total_multiset_extension = total_on_multiset_extension where X = UNIV
begin

lemma inj_to_mset: "inj to_mset"
  using inj_on_to_mset 
  by simp

lemmas inj_on_to_mset = inj_on_subset[OF inj_to_mset subset_UNIV]

sublocale total_strict_order "(\<prec>\<^sub>m)"
  using totalp_on_subset
  by unfold_locales fastforce

end

locale restricted_term_ordering_lifting =
  fixes
    less\<^sub>t :: "'t \<Rightarrow> 't \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) and
    X :: "'t set"
  assumes
    less\<^sub>t_transp [intro]: "transp (\<prec>\<^sub>t)" and
    less\<^sub>t_asymp [intro]: "asymp (\<prec>\<^sub>t)" and
    less\<^sub>t_wfp_on [intro]: "wfp_on X (\<prec>\<^sub>t)" and
    less\<^sub>t_totalp_on [intro]: "totalp_on X (\<prec>\<^sub>t)" 
begin

abbreviation less_eq\<^sub>t where
  "less_eq\<^sub>t \<equiv> (\<prec>\<^sub>t)\<^sup>=\<^sup>="

notation less_eq\<^sub>t (infix "\<preceq>\<^sub>t" 50)

sublocale term_order: total_on_strict_order "(\<prec>\<^sub>t)"
  by unfold_locales auto

abbreviation literal_order_restriction where 
  "literal_order_restriction \<equiv> {b. set_mset (mset_lit b) \<subseteq> X}"

sublocale literal_order: total_on_multiset_extension where R = "(\<prec>\<^sub>t)" and to_mset = mset_lit 
  using inj_mset_lit
  by unfold_locales (auto simp: inj_on_def)

abbreviation less\<^sub>l where
  "less\<^sub>l \<equiv> literal_order.multiset_extension"

notation less\<^sub>l (infix "\<prec>\<^sub>l" 50) 

abbreviation less_eq\<^sub>l where
  "less_eq\<^sub>l \<equiv> (\<prec>\<^sub>l)\<^sup>=\<^sup>="

notation less_eq\<^sub>l (infix "\<preceq>\<^sub>l" 50)

lemmas less\<^sub>l_def = literal_order.multiset_extension_def

sublocale clause_order: total_on_multiset_extension where 
  R = "(\<prec>\<^sub>l)" and to_mset = "\<lambda>x. x" and X = literal_order_restriction
  by unfold_locales simp

abbreviation less\<^sub>c where
  "less\<^sub>c \<equiv> clause_order.multiset_extension"

notation less\<^sub>c (infix "\<prec>\<^sub>c" 50) 

abbreviation less_eq\<^sub>c where
  "less_eq\<^sub>c \<equiv> (\<prec>\<^sub>c)\<^sup>=\<^sup>="

notation less_eq\<^sub>c (infix "\<preceq>\<^sub>c" 50)

lemmas less\<^sub>c_def = clause_order.multiset_extension_def

abbreviation is_maximal\<^sub>l :: "'t uprod literal \<Rightarrow> 't uprod clause \<Rightarrow> bool" where
  "is_maximal\<^sub>l L M \<equiv> is_maximal_in_mset_wrt (\<prec>\<^sub>l) M L"

abbreviation is_strictly_maximal\<^sub>l :: "'t uprod literal \<Rightarrow> 't uprod clause \<Rightarrow> bool" where
  "is_strictly_maximal\<^sub>l L M \<equiv> is_strictly_maximal_in_mset_wrt (\<prec>\<^sub>l) M L"

lemmas is_maximal\<^sub>l_def = literal_order.is_maximal_in_mset_iff

lemmas is_strictly_maximal\<^sub>l_def = literal_order.is_strictly_maximal_in_mset_iff

lemmas is_maximal\<^sub>l_if_is_strictly_maximal\<^sub>l = 
  literal_order.is_maximal_in_mset_if_is_strictly_maximal_in_mset

lemma maximal\<^sub>l_in_clause:
  assumes "is_maximal\<^sub>l literal clause"
  shows "literal \<in># clause"
  using assms 
  unfolding is_maximal\<^sub>l_def
  by(rule conjunct1)

lemma strictly_maximal\<^sub>l_in_clause:
  assumes "is_strictly_maximal\<^sub>l literal clause"
  shows "literal \<in># clause"
  using assms  
  unfolding is_strictly_maximal\<^sub>l_def
  by(rule conjunct1)

lemma is_maximal\<^sub>l_empty [simp]: 
  assumes "is_maximal\<^sub>l literal {#}"  
  shows False
  using assms maximal\<^sub>l_in_clause
  by fastforce

lemma is_strictly_maximal\<^sub>l_empty [simp]: 
  assumes "is_strictly_maximal\<^sub>l literal {#}"  
  shows False
  using assms strictly_maximal\<^sub>l_in_clause
  by fastforce

end

locale total_wellfounded_multiset_extension = 
  wellfounded_multiset_extension + total_multiset_extension

locale term_ordering_lifting = restricted_term_ordering_lifting where X = UNIV
begin

sublocale term_order: wellfounded_strict_order "(\<prec>\<^sub>t)"
  using wfp_on_subset
  by unfold_locales auto

sublocale term_order: total_strict_order "(\<prec>\<^sub>t)"
  by unfold_locales

sublocale literal_order: wellfounded_multiset_extension where R = "(\<prec>\<^sub>t)" and to_mset = mset_lit
  by unfold_locales

sublocale literal_order: total_multiset_extension where R = "(\<prec>\<^sub>t)" and to_mset = mset_lit
  by unfold_locales

sublocale clause_order: wellfounded_multiset_extension where R = "(\<prec>\<^sub>l)"  and to_mset = "\<lambda>x. x" 
  by unfold_locales

sublocale clause_order: total_multiset_extension where R = "(\<prec>\<^sub>l)" and to_mset = "\<lambda>x. x"
  by unfold_locales simp

end

locale grounded_term_ordering_lifting = restricted_term_ordering_lifting 
  where X = "range from_ground" for from_ground :: "'g \<Rightarrow> 't" +
  assumes
    inj_from_ground: "inj from_ground" 
begin

definition less\<^sub>t\<^sub>G :: "'g \<Rightarrow> 'g \<Rightarrow> bool" (infix "\<prec>\<^sub>t\<^sub>G" 50) where
  "term\<^sub>G\<^sub>1 \<prec>\<^sub>t\<^sub>G term\<^sub>G\<^sub>2 \<equiv> from_ground term\<^sub>G\<^sub>1 \<prec>\<^sub>t from_ground term\<^sub>G\<^sub>2"

sublocale ground: term_ordering_lifting "(\<prec>\<^sub>t\<^sub>G)"
proof unfold_locales
  show "transp (\<prec>\<^sub>t\<^sub>G)"
    unfolding less\<^sub>t\<^sub>G_def
    using term_order.dual_order.strict_trans transp_def by blast
next
  show "asymp (\<prec>\<^sub>t\<^sub>G)"
    unfolding less\<^sub>t\<^sub>G_def
    by (simp add: asympI)
next
  show "wfp (\<prec>\<^sub>t\<^sub>G)"
    unfolding less\<^sub>t\<^sub>G_def
    by (metis less\<^sub>t_wfp_on wfp_on_image)
next
  show "totalp (\<prec>\<^sub>t\<^sub>G)"
    unfolding less\<^sub>t\<^sub>G_def
    using inj_from_ground totalp_on_image by blast
qed

end

end
