theory Term_Ordering_Lifting
  imports 
    Clausal_Calculus_Extra 
    Min_Max_Least_Greatest_Multiset
    Functional_Substitution_Lifting
    Nonground_Clause
begin

locale relation_restriction = 
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and lift :: "'b \<Rightarrow> 'a" (* TODO: Name *)
  assumes inj_lift [intro]: "inj lift"
begin

definition R\<^sub>r :: "'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "R\<^sub>r b b' \<equiv> R (lift b) (lift b')"

end

locale strict_order = 
  fixes
    less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes
    transp [intro]: "transp (\<prec>)" and
    asymp [intro]: "asymp (\<prec>)"
begin

abbreviation less_eq where "less_eq \<equiv> (\<prec>)\<^sup>=\<^sup>="

notation less_eq (infix "\<preceq>" 50)
 
sublocale order "(\<preceq>)" "(\<prec>)"
  by(rule order_reflclp_if_transp_and_asymp[OF transp asymp])

end

(* TODO: name *)
locale strict_order_restriction = strict_order + relation_restriction where R = "(\<prec>)"
begin

abbreviation "less\<^sub>r \<equiv> R\<^sub>r"

notation less\<^sub>r (infix "\<prec>\<^sub>r" 50)

(* TODO: Without name! *)
sublocale restriction: strict_order "(\<prec>\<^sub>r)"
  by unfold_locales (auto simp: R\<^sub>r_def transp_def)

notation restriction.less_eq (infix "\<preceq>\<^sub>r" 50)

end

locale restricted_wellfounded_strict_order = strict_order +
  fixes restriction
  assumes wfp_on [intro]: "wfp_on restriction (\<prec>)"

locale wellfounded_strict_order = strict_order +
  assumes wfp [intro]: "wfp (\<prec>)"
begin

sublocale restricted_wellfounded_strict_order "(\<prec>)" UNIV
  by unfold_locales (rule wfp)

end

locale wellfounded_strict_order_restriction = 
  strict_order_restriction +
  restricted_wellfounded_strict_order where restriction = "range lift" and less = "(\<prec>)"
begin

sublocale restriction: wellfounded_strict_order "(\<prec>\<^sub>r)"
proof unfold_locales
  show "wfp (\<prec>\<^sub>r)"
    using wfp_on_if_convertible_to_wfp_on[OF wfp_on]
    unfolding R\<^sub>r_def
    by simp
qed

end

locale restricted_total_strict_order = strict_order +
  fixes restriction
  assumes totalp_on [intro]: "totalp_on restriction (\<prec>)"

locale total_strict_order = strict_order +
  assumes totalp [intro]: "totalp (\<prec>)"
begin

sublocale linorder "(\<preceq>)" "(\<prec>)"
  using totalpD
  by unfold_locales fastforce

sublocale restricted_total_strict_order "(\<prec>)" UNIV
  by unfold_locales (rule totalp)

end

locale total_strict_order_restriction = 
  strict_order_restriction + 
  restricted_total_strict_order where restriction = "range lift" and less = "(\<prec>)"
begin

sublocale restriction: total_strict_order "(\<prec>\<^sub>r)"
proof unfold_locales
  show "totalp (\<prec>\<^sub>r)"
    using totalp_on inj_lift
    unfolding R\<^sub>r_def totalp_on_def inj_def
    by blast
qed

end

locale multiset_extension = base: strict_order +
  fixes to_mset :: "'b \<Rightarrow> 'a multiset"
begin

definition multiset_extension :: "'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "multiset_extension b1 b2 \<equiv> multp (\<prec>) (to_mset b1) (to_mset b2)"

notation multiset_extension (infix "\<prec>\<^sub>m" 50)

sublocale strict_order "(\<prec>\<^sub>m)"
proof unfold_locales
  show "transp (\<prec>\<^sub>m)"
    using transp_multp[OF base.transp]
    unfolding multiset_extension_def transp_on_def
    by blast
next
  show "asymp (\<prec>\<^sub>m)"
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
  show "wfp (\<prec>\<^sub>m)"
    unfolding multiset_extension_def
    using wfp_multp
    by (metis (no_types, lifting) base.wfp top_greatest wfp_if_convertible_to_wfp wfp_on_subset)
qed

end

locale restricted_total_multiset_extension = 
  base: restricted_total_strict_order + multiset_extension +
  assumes inj_on_to_mset: "inj_on to_mset {b. set_mset (to_mset b) \<subseteq> restriction}"
begin

sublocale restricted_total_strict_order "(\<prec>\<^sub>m)" "{b. set_mset (to_mset b) \<subseteq> restriction}"
proof unfold_locales
  have "totalp_on {b. set_mset b \<subseteq> restriction} (multp (\<prec>))"
    using totalp_on_multp[OF base.totalp_on base.transp]
    by fastforce

  then show "totalp_on {b. set_mset (to_mset b) \<subseteq> restriction} (\<prec>\<^sub>m)"
    using inj_on_to_mset
    unfolding multiset_extension_def totalp_on_def inj_on_def
    by auto
qed

end

locale grounded_order = 
  strict_order_restriction where lift = "from_ground :: 'expr\<^sub>G \<Rightarrow> 'expr" + 
  grounding
begin

lemma to_ground_less\<^sub>r [simp]: 
  assumes "is_ground e" and "is_ground e'"
  shows "to_ground e \<prec>\<^sub>r to_ground e' \<longleftrightarrow> e \<prec> e'"
  by (simp add: assms R\<^sub>r_def) (* TODO: Name R\<^sub>r_def *)

lemma to_ground_less_eq\<^sub>r [simp]:
  assumes "is_ground e" and "is_ground e'" 
  shows "to_ground e \<preceq>\<^sub>r to_ground e' \<longleftrightarrow> e \<preceq> e'"
  using assms obtain_grounding
  by fastforce

lemma less_eq\<^sub>r_from_ground [simp]:
   "e\<^sub>G \<preceq>\<^sub>r e\<^sub>G' \<longleftrightarrow> from_ground e\<^sub>G \<preceq> from_ground e\<^sub>G'"
  unfolding R\<^sub>r_def
  by (simp add: inj_eq inj_lift)
  
end

locale ground_subst_stable_grounded_order = grounded_order + 
  assumes 
    less_ground_subst_stability: 
      "\<And>e\<^sub>1 e\<^sub>2 \<gamma>.
        is_ground (e\<^sub>1 \<cdot> \<gamma>) \<Longrightarrow>
        is_ground (e\<^sub>2 \<cdot> \<gamma>) \<Longrightarrow>
        e\<^sub>1 \<prec> e\<^sub>2 \<Longrightarrow>
        e\<^sub>1 \<cdot> \<gamma> \<prec> e\<^sub>2 \<cdot> \<gamma>"
begin

(* TODO: Names *)
lemma less_eq_ground_subst_stability:
  assumes "is_ground (term\<^sub>1 \<cdot> \<gamma>)" "is_ground (term\<^sub>2 \<cdot> \<gamma>)"  "term\<^sub>1 \<preceq> term\<^sub>2"
  shows "term\<^sub>1 \<cdot> \<gamma> \<preceq> term\<^sub>2 \<cdot> \<gamma>"
  using less_ground_subst_stability[OF assms(1, 2)] assms(3)
  by auto

lemma less\<^sub>t_less_eq\<^sub>t_ground_subst_stability:
  assumes 
    "is_ground (term\<^sub>1 \<cdot> \<gamma>)"
    "is_ground (term\<^sub>2 \<cdot> \<gamma>)"
    "term\<^sub>1 \<cdot> \<gamma> \<prec> term\<^sub>2 \<cdot> \<gamma>"
  shows
    "\<not> term\<^sub>2 \<preceq> term\<^sub>1"
proof
  assume assumption: "term\<^sub>2 \<preceq> term\<^sub>1"

  have "term\<^sub>2 \<cdot> \<gamma> \<preceq> term\<^sub>1 \<cdot> \<gamma>"
    using less_eq_ground_subst_stability[OF 
            assms(2, 1)
            assumption
           ].

  then show False 
    using assms(3) by order
qed


end


locale less_subst_upd_grounded_order =
  fixes base_less less base_is_ground is_ground subst vars
  assumes
    less_subst_upd:
    "\<And>update x \<gamma> expr. 
      base_is_ground update \<Longrightarrow>
      base_less update (\<gamma> x) \<Longrightarrow> 
      is_ground (subst expr \<gamma>) \<Longrightarrow>
      x \<in> vars expr \<Longrightarrow>
      less (subst expr (\<gamma>(x := update))) (subst expr \<gamma>)"

(* TODO: Name *)
locale grounded_total_strict_order = 
  total_strict_order_restriction where lift = "from_ground :: 'expr\<^sub>G \<Rightarrow> 'expr" +
  grounded_order
begin

lemma not_less_eq [simp]: 
  assumes "is_ground e" and "is_ground e'"
  shows "\<not> e' \<preceq> e \<longleftrightarrow> e \<prec> e'"
  using assms totalp_on
  unfolding totalp_on_def is_ground_iff_range_from_ground
  by auto
  
end

locale multiset_extension_restriction = 
  sub: strict_order_restriction where lift = "sub_from_ground :: 'sub\<^sub>G \<Rightarrow> 'sub" + 
  multiset_extension where to_mset = to_mset +
  grounding_lifting where id_subst = id_subst and to_set = to_set and to_set_ground = to_set_ground
for 
  to_mset :: "'expr \<Rightarrow> 'sub multiset" and 
  id_subst :: "'var \<Rightarrow> 'base" and
  to_set :: "'expr \<Rightarrow> 'sub set" and
  to_set_ground :: "'expr\<^sub>G \<Rightarrow> 'sub\<^sub>G set" +
assumes 
  to_mset_to_set: "\<And>expr. set_mset (to_mset expr) = to_set expr" and
  inj_to_mset: "inj to_mset" (* TODO: *)
begin

sublocale strict_order_restriction "(\<prec>\<^sub>m)" from_ground
  by(unfold_locales)(rule inj_from_ground)

end

(* TODO: Name *)
locale total_multiset_extension_restriction = 
  multiset_extension_restriction +
  sub: total_strict_order_restriction where lift = "sub_from_ground"
begin

sublocale total_strict_order_restriction "(\<prec>\<^sub>m)" from_ground
proof unfold_locales
  have "totalp_on {expr. set_mset expr \<subseteq> range sub_from_ground} (multp (\<prec>))"
    using sub.totalp_on totalp_on_multp by fastforce

  then have "totalp_on {expr. set_mset (to_mset expr) \<subseteq> range sub_from_ground} (\<prec>\<^sub>m)"
    using inj_to_mset
    unfolding inj_def multiset_extension_def totalp_on_def
    by blast

  then show "totalp_on (range from_ground) (\<prec>\<^sub>m)"
    unfolding multiset_extension_def totalp_on_def from_ground_def
    by (simp add: image_mono to_mset_to_set)
qed
  
end

locale based_multiset_extension_restriction = 
  based_functional_substitution_lifting where base_vars = base_vars +
  multiset_extension_restriction +
  sub: strict_order +
  base: strict_order where less = base_less 
for base_vars :: "'base \<Rightarrow> 'var set" and base_less :: "'base \<Rightarrow> 'base \<Rightarrow> bool"
 

(* TODO: Name + totality not needed! *)
locale total_multiset_extension_restriction_stable = 
  multiset_extension_restriction + 
  sub: ground_subst_stable_grounded_order where 
  less = less and subst = sub_subst and vars = sub_vars and from_ground = sub_from_ground and 
  to_ground = sub_to_ground +
assumes to_mset_map: "\<And>f b. to_mset (map f b) = image_mset f (to_mset b)"
begin

sublocale ground_subst_stable_grounded_order where 
  less = "(\<prec>\<^sub>m)" and subst = subst and vars = vars and from_ground = from_ground and 
  to_ground = to_ground
proof unfold_locales

  fix e\<^sub>1 e\<^sub>2 \<gamma> 
  assume "is_ground (e\<^sub>1 \<cdot> \<gamma>)" "is_ground (e\<^sub>2 \<cdot> \<gamma>)" and a: "e\<^sub>1 \<prec>\<^sub>m e\<^sub>2" 

  moreover then have "monotone_on (set_mset (to_mset e\<^sub>1 + to_mset e\<^sub>2)) (\<prec>) (\<prec>) (\<lambda>sub. sub \<cdot>\<^sub>s \<gamma>)"
    using monotone_onI sub.less_ground_subst_stability
    by (smt (verit, best) to_mset_to_set to_set_is_ground_subst union_iff)
  
  then show "e\<^sub>1 \<cdot> \<gamma> \<prec>\<^sub>m e\<^sub>2 \<cdot> \<gamma>"
    unfolding multiset_extension_def subst_def to_mset_map
    by(rule multp_map_strong[OF sub.transp _ a[unfolded multiset_extension_def]])
qed

end


locale multiset_extension_restriction_upd = 
  based_multiset_extension_restriction +
  sub: less_subst_upd_grounded_order where 
  less = less and base_is_ground = base.is_ground and is_ground = sub.is_ground
  and vars = sub_vars and subst = sub_subst +
  assumes to_mset_map: "\<And>f b. to_mset (map f b) = image_mset f (to_mset b)"
begin 


sublocale less_subst_upd_grounded_order where 
  less = "(\<prec>\<^sub>m)" and base_is_ground = base.is_ground and is_ground = is_ground
  and vars = vars and subst = subst 
proof unfold_locales
  fix update x \<gamma> expr
  assume assms: 
    "base.is_ground update" "base_less update (\<gamma> x)" "is_ground (expr \<cdot> \<gamma>)" "x \<in> vars expr"

  moreover then have "\<forall>sub \<in># to_mset expr. sub.less_eq (sub \<cdot>\<^sub>s \<gamma>(x := update)) (sub \<cdot>\<^sub>s \<gamma>)" (* TODO: sub.less_eq *)
    using sub.less_subst_upd sub.subst_reduntant_upd
    by (metis sub.order.refl sub.order.strict_iff_not to_mset_to_set to_set_is_ground_subst)

  moreover have "\<exists>sub \<in># to_mset expr. sub \<cdot>\<^sub>s \<gamma>(x := update) \<prec> (sub \<cdot>\<^sub>s \<gamma>)"
    using sub.less_subst_upd assms
    unfolding vars_def subst_def to_mset_to_set
    by fastforce

  ultimately show "expr \<cdot> \<gamma>(x := update) \<prec>\<^sub>m expr \<cdot> \<gamma> "
    unfolding multiset_extension_def subst_def to_mset_map
    using multp_all_lesseq_ex_less[OF sub.asymp sub.transp]
    by meson
qed

end

locale total_multiset_extension = restricted_total_multiset_extension where restriction = UNIV
begin

lemma inj_to_mset: "inj to_mset"
  using inj_on_to_mset 
  by simp

lemmas inj_on_to_mset = inj_on_subset[OF inj_to_mset subset_UNIV]

sublocale total_strict_order "(\<prec>\<^sub>m)"
  using totalp_on_subset
  by unfold_locales fastforce

end

locale total_wellfounded_multiset_extension = 
  wellfounded_multiset_extension + total_multiset_extension

(* TODO: Name*)
locale literal_order = strict_order where less = less for 
  less :: "'t uprod literal \<Rightarrow> 't uprod literal \<Rightarrow> bool"
begin

abbreviation is_maximal\<^sub>l :: "'t uprod literal \<Rightarrow> 't uprod clause \<Rightarrow> bool" where
  "is_maximal\<^sub>l L M \<equiv> is_maximal_in_mset_wrt less M L"

abbreviation is_strictly_maximal\<^sub>l :: "'t uprod literal \<Rightarrow> 't uprod clause \<Rightarrow> bool" where
  "is_strictly_maximal\<^sub>l L M \<equiv> is_strictly_maximal_in_mset_wrt less M L"

lemmas is_maximal\<^sub>l_def = is_maximal_in_mset_iff

lemmas is_strictly_maximal\<^sub>l_def = is_strictly_maximal_in_mset_iff

lemmas is_maximal\<^sub>l_if_is_strictly_maximal\<^sub>l = is_maximal_in_mset_if_is_strictly_maximal_in_mset

lemma maximal\<^sub>l_in_clause:
  assumes "is_maximal\<^sub>l l C"
  shows "l \<in># C"
  using assms 
  unfolding is_maximal\<^sub>l_def
  by(rule conjunct1)

lemma strictly_maximal\<^sub>l_in_clause:
  assumes "is_strictly_maximal\<^sub>l l C"
  shows "l \<in># C"
  using assms  
  unfolding is_strictly_maximal\<^sub>l_def
  by(rule conjunct1)

lemma is_maximal\<^sub>l_empty [simp]: "\<not>is_maximal\<^sub>l l {#}"  
  using maximal\<^sub>l_in_clause
  by fastforce

lemma is_strictly_maximal\<^sub>l_empty [simp]: "\<not>is_strictly_maximal\<^sub>l l {#}"
  using strictly_maximal\<^sub>l_in_clause
  by fastforce

end

locale restricted_term_ordering_lifting =
  term_order: restricted_total_strict_order where less = "(\<prec>\<^sub>t)" +
  term_order: restricted_wellfounded_strict_order where less = "(\<prec>\<^sub>t)"
  for
    less\<^sub>t :: "'t \<Rightarrow> 't \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) 
begin

notation term_order.less_eq (infix "\<preceq>\<^sub>t" 50)

abbreviation literal_order_restriction where 
  "literal_order_restriction \<equiv> {b. set_mset (mset_lit b) \<subseteq> restriction}"

sublocale literal_order: restricted_total_multiset_extension where 
  less = "(\<prec>\<^sub>t)" and to_mset = mset_lit
  using inj_mset_lit
  by unfold_locales (auto simp: inj_on_def)

notation literal_order.multiset_extension (infix "\<prec>\<^sub>l" 50)
notation literal_order.less_eq (infix "\<preceq>\<^sub>l" 50)

lemmas less\<^sub>l_def = literal_order.multiset_extension_def

sublocale clause_order: restricted_total_multiset_extension where 
  less = "(\<prec>\<^sub>l)" and to_mset = "\<lambda>x. x" and restriction = literal_order_restriction
  by unfold_locales auto

notation clause_order.multiset_extension (infix "\<prec>\<^sub>c" 50) 
notation clause_order.less_eq (infix "\<preceq>\<^sub>c" 50)

lemmas less\<^sub>c_def = clause_order.multiset_extension_def

sublocale literal_order "(\<prec>\<^sub>l)"
  by unfold_locales

end

locale grounded_term_ordering_lifting =
  restricted_term_ordering_lifting where restriction = "range term.from_ground"
begin

sublocale term_order: 
  total_strict_order_restriction where less = less\<^sub>t and lift = term.from_ground
  apply unfold_locales
  by (simp add: inj_term_of_gterm)

sublocale term_order: grounded_total_strict_order where 
  less = less\<^sub>t and from_ground = term.from_ground and comp_subst = "(\<odot>)" and subst = "(\<cdot>t)" and
  vars = term.vars and id_subst = Var and to_ground = term.to_ground
  by unfold_locales

(* TODO *)
notation term_order.R\<^sub>r (infix "\<prec>\<^sub>t\<^sub>G" 50)
notation term_order.restriction.less_eq (infix "\<preceq>\<^sub>t\<^sub>G" 50)
lemmas less\<^sub>t\<^sub>G_def = term_order.R\<^sub>r_def

(* TODO: Duplication *)
sublocale literal_order: total_multiset_extension_restriction where 
  less = "(\<prec>\<^sub>t)" and comp_subst = "(\<odot>)" and sub_to_ground = term.to_ground and 
  sub_from_ground = term.from_ground and sub_vars = term.vars and sub_subst = "(\<cdot>t)" and 
  map = map_literal_term and to_ground_map = map_literal_term and 
  from_ground_map = map_literal_term and ground_map = map_literal_term and to_mset = mset_lit and 
  id_subst = Var and to_set = literal_to_term_set and to_set_ground = literal_to_term_set
  using inj_mset_lit term.inj_from_ground
  by unfold_locales auto

(* TODO! \<longrightarrow> Same for clause
sublocale literal_order: grounded_total_strict_order where 
  less = "(\<prec>\<^sub>l)" and from_ground = literal.from_ground and comp_subst = "(\<odot>)" and subst = "(\<cdot>l)" and
  vars = literal.vars and id_subst = Var and to_ground = literal.to_ground
  by unfold_locales*)

notation literal_order.R\<^sub>r (infix "\<prec>\<^sub>l\<^sub>G" 50)
notation literal_order.restriction.less_eq (infix "\<preceq>\<^sub>l\<^sub>G" 50)

lemmas less\<^sub>l\<^sub>G_def = literal_order.R\<^sub>r_def


sublocale clause: total_multiset_extension_restriction where 
  less = "(\<prec>\<^sub>l)" and to_mset = "\<lambda>x. x" and comp_subst = "(\<odot>)" and sub_to_ground = literal'.to_ground and 
  sub_from_ground = literal'.from_ground and sub_vars = literal'.vars and sub_subst = "(\<cdot>l)" and 
  map = image_mset and to_ground_map = image_mset and 
  from_ground_map = image_mset and ground_map = image_mset and 
  id_subst = Var and to_set = set_mset and to_set_ground = set_mset
  by unfold_locales auto

notation clause.R\<^sub>r (infix "\<prec>\<^sub>c\<^sub>G" 50)
notation clause.restriction.less_eq (infix "\<preceq>\<^sub>c\<^sub>G" 50)

lemmas less\<^sub>c\<^sub>G_def = clause.R\<^sub>r_def

sublocale restriction: literal_order "(\<prec>\<^sub>l\<^sub>G)"
  by unfold_locales

(* TODO!!  *)
lemma ground_is_maximal\<^sub>l_iff_is_maximal\<^sub>l: 
  "restriction.is_maximal\<^sub>l l\<^sub>G C\<^sub>G \<longleftrightarrow> is_maximal\<^sub>l (literal.from_ground l\<^sub>G) (clause.from_ground C\<^sub>G)"
   unfolding 
    is_maximal\<^sub>l_def
    restriction.is_maximal\<^sub>l_def
    clause.ground_sub_in_ground[symmetric]
   by (smt (verit, best) atom.from_ground_def image_iff less\<^sub>l\<^sub>G_def literal'.from_ground_def literal.from_ground_def literal.map_cong0 literal_order.dual_order.strict_iff_order clause.ground_sub_in_ground clause.to_set_from_ground)
   
lemma ground_is_strictly_maximal\<^sub>l_iff_is_strictly_maximal\<^sub>l:
  "restriction.is_strictly_maximal\<^sub>l l\<^sub>G C\<^sub>G \<longleftrightarrow> 
    is_strictly_maximal\<^sub>l (literal.from_ground l\<^sub>G) (clause.from_ground C\<^sub>G)"
  unfolding 
    restriction.is_strictly_maximal\<^sub>l_def
    is_strictly_maximal\<^sub>l_def
    clause.ground_sub_in_ground[symmetric]
    remove1_mset_literal_from_ground
    clause.ground_sub
  apply auto
  apply (metis (mono_tags, lifting) atom.from_ground_def image_iff literal'.from_ground_def literal.from_ground_def literal.map_cong0 local.clause.to_set_from_ground)
  apply (smt (verit, best) Nonground_Clause.clause.from_ground_def atom.from_ground_def image_iff image_mset_cong2 less\<^sub>l\<^sub>G_def literal'.from_ground_def literal.from_ground_def literal.map_cong0 local.clause.from_ground_def local.clause.to_set_from_ground remove1_mset_literal_from_ground)
  apply (metis Nonground_Clause.clause.from_ground_def Nonground_Clause.clause.ground_sub_in_ground atom.from_ground_def image_mset_cong2 literal'.from_ground_def literal.from_ground_def literal.map_cong0 local.clause.from_ground_def remove1_mset_literal_from_ground)
  apply (metis atom.from_ground_def literal'.from_ground_def literal.from_ground_def literal.map_cong0 local.clause.ground_sub_in_ground)
  apply (metis (mono_tags, lifting) Nonground_Clause.clause.from_ground_def Nonground_Clause.clause.ground_sub_in_ground atom.from_ground_def image_mset_cong2 less\<^sub>l\<^sub>G_def literal'.from_ground_def literal.from_ground_def literal.map_cong0 local.clause.from_ground_def remove1_mset_literal_from_ground)
  by (metis (mono_tags, lifting) Nonground_Clause.clause.from_ground_def Nonground_Clause.clause.to_set_from_ground atom.from_ground_def image_iff image_mset_cong2 literal'.from_ground_def literal.from_ground_def literal.map_cong0 local.clause.from_ground_def remove1_mset_literal_from_ground)
 
end


locale term_ordering_lifting =  
  restricted_term_ordering_lifting where restriction = UNIV +
  term_order: wellfounded_strict_order "(\<prec>\<^sub>t)" + 
  term_order: total_strict_order "(\<prec>\<^sub>t)"
begin

sublocale literal_order: total_wellfounded_multiset_extension where 
  less = "(\<prec>\<^sub>t)" and to_mset = mset_lit
  by unfold_locales

sublocale clause_order: total_wellfounded_multiset_extension where 
  less = "(\<prec>\<^sub>l)"  and to_mset = "\<lambda>x. x" 
  by unfold_locales simp

end


end
