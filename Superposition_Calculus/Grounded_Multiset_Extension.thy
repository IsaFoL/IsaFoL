theory Grounded_Multiset_Extension
  imports Grounded_Order Multiset_Extension
begin

section \<open>Grounded Multiset Extensions\<close>

(* TODO:*)
lemma "refl R \<Longrightarrow> refl (R\<^sup>+)"
  by (simp add: r_into_trancl' refl_on_def)

lemma not_reflp_multp\<^sub>D\<^sub>M: "\<not> reflp (multp\<^sub>D\<^sub>M R)"
  unfolding multp\<^sub>D\<^sub>M_def reflp_def
  by force

lemma not_less_empty_multp\<^sub>D\<^sub>M: "\<not> multp\<^sub>D\<^sub>M R X {#}"
  by (simp add: multp\<^sub>D\<^sub>M_def)

lemma not_reflp_multp\<^sub>H\<^sub>O: "\<not> reflp (multp\<^sub>H\<^sub>O R)"
  unfolding multp\<^sub>H\<^sub>O_def reflp_def
  by simp

lemma not_less_empty_multp\<^sub>H\<^sub>O: "\<not> multp\<^sub>H\<^sub>O R X {#}"
  by (simp add: multp\<^sub>H\<^sub>O_def)

lemma not_refl_mult: "\<not> refl (mult R)"
  unfolding refl_on_def mult_def
  by (meson UNIV_I not_less_empty trancl.cases)

lemma not_less_empty_mult: "(X, {#}) \<notin> mult R"
  by (metis mult_def not_less_empty tranclD2)

lemma empty_less_mult: "X \<noteq> {#} \<Longrightarrow> ({#}, X) \<in> mult R"
  using subset_implies_mult
  by force

lemma not_reflp_multp: "\<not> reflp (multp R)"
  using not_refl_mult
  unfolding multp_def reflp_refl_eq
  by blast

lemma empty_less_multp: "X \<noteq> {#} \<Longrightarrow> multp R {#} X"
  by (simp add: subset_implies_multp subset_mset.not_eq_extremum)

lemma not_less_empty_multp: "\<not> multp R X {#}"
  using not_less_empty_mult
  unfolding multp_def
  by blast

locale functional_substitution_multiset_extension =
  sub: strict_order where less = "(\<prec>) :: 'sub \<Rightarrow> 'sub \<Rightarrow> bool" +
  multiset_extension where to_mset = to_mset +
  functional_substitution_lifting where id_subst = id_subst and to_set = to_set
for 
  to_mset :: "'expr \<Rightarrow> 'sub multiset" and
  id_subst :: "'var \<Rightarrow> 'base" and
  to_set :: "'expr \<Rightarrow> 'sub set" +
assumes
    (* TODO: Does it make sense to have these in separate locales? *)
  to_mset_to_set: "\<And>expr. set_mset (to_mset expr) = to_set expr" and
  to_mset_map: "\<And>f b. to_mset (map f b) = image_mset f (to_mset b)" and 
  inj_to_mset: "inj to_mset"
begin

(* TODO *)
no_notation less_eq (infix "\<preceq>" 50)
notation sub.less_eq (infix "\<preceq>" 50)

(* TODO: Names *)
lemma all_less_eq:
  assumes "\<forall>sub \<in># to_mset expr. sub \<cdot>\<^sub>s \<sigma>' \<preceq> sub \<cdot>\<^sub>s \<sigma>"
  shows "expr \<cdot> \<sigma>' \<preceq>\<^sub>m expr \<cdot> \<sigma>"
  using multp_all_less_eq[OF sub.asymp sub.transp assms] inj_to_mset
  unfolding multiset_extension_def subst_def inj_def
  by(auto simp: to_mset_map)

lemma all_less_eq_ex_less:
  assumes 
    "\<forall>sub\<in>#to_mset expr. sub \<cdot>\<^sub>s \<sigma>' \<preceq> sub \<cdot>\<^sub>s \<sigma>"
    "\<exists>sub\<in>#to_mset expr. sub \<cdot>\<^sub>s \<sigma>' \<prec> sub \<cdot>\<^sub>s \<sigma>"
  shows 
    "expr \<cdot> \<sigma>' \<prec>\<^sub>m expr \<cdot> \<sigma>"
  using multp_all_less_eq_ex_less[OF sub.asymp sub.transp assms]
  unfolding multiset_extension_def subst_def to_mset_map.

end

locale grounded_multiset_extension =
  grounding_lifting where 
  id_subst = "id_subst :: 'var \<Rightarrow> 'base" and to_set = "to_set :: 'expr \<Rightarrow> 'sub set" and 
  to_set_ground = to_set_ground +
  functional_substitution_multiset_extension where to_mset = to_mset
for 
  to_mset :: "'expr \<Rightarrow> 'sub multiset" and 
  to_set_ground :: "'expr\<^sub>G \<Rightarrow> 'sub\<^sub>G set"
begin

sublocale strict_order_restriction "(\<prec>\<^sub>m)" from_ground 
  by unfold_locales (rule inj_from_ground)

end

(* TODO: Name \<rightarrow> restriction is just total *)
locale total_grounded_multiset_extension = 
  grounded_multiset_extension +
  sub: total_strict_order_restriction where lift = "sub_from_ground"
begin

sublocale total_strict_order_restriction "(\<prec>\<^sub>m)" from_ground
proof unfold_locales
  have "totalp_on {expr. set_mset expr \<subseteq> range sub_from_ground} (multp (\<prec>))"
    using sub.totalp totalp_on_multp 
    by force

  then have "totalp_on {expr. set_mset (to_mset expr) \<subseteq> range sub_from_ground} (\<prec>\<^sub>m)"
    using inj_to_mset
    unfolding inj_def multiset_extension_def totalp_on_def
    by blast

  then show "totalp_on (range from_ground) (\<prec>\<^sub>m)"
    unfolding multiset_extension_def totalp_on_def from_ground_def
    by (simp add: image_mono to_mset_to_set)
qed
  
end

locale based_grounded_multiset_extension = 
  based_functional_substitution_lifting where base_vars = base_vars +
  grounded_multiset_extension +
  base: strict_order where less = base_less 
for 
  base_vars :: "'base \<Rightarrow> 'var set" and 
  base_less :: "'base \<Rightarrow> 'base \<Rightarrow> bool"

subsection \<open>Ground substitution stability\<close>

locale ground_subst_stable_total_multiset_extension = 
  grounded_multiset_extension + 
  sub: ground_subst_stable_grounded_order where 
  less = less and subst = sub_subst and vars = sub_vars and from_ground = sub_from_ground and 
  to_ground = sub_to_ground
begin

sublocale ground_subst_stable_grounded_order where 
  less = "(\<prec>\<^sub>m)" and subst = subst and vars = vars and from_ground = from_ground and 
  to_ground = to_ground
proof unfold_locales

  fix expr\<^sub>1 expr\<^sub>2 \<gamma>

  assume grounding: "is_ground (expr\<^sub>1 \<cdot> \<gamma>)" "is_ground (expr\<^sub>2 \<cdot> \<gamma>)" and less: "expr\<^sub>1 \<prec>\<^sub>m expr\<^sub>2"

  show "expr\<^sub>1 \<cdot> \<gamma> \<prec>\<^sub>m expr\<^sub>2 \<cdot> \<gamma>"
  proof(
      unfold multiset_extension_def subst_def to_mset_map, 
      rule multp_map_strong[OF sub.transp _ less[unfolded multiset_extension_def]])

    show "monotone_on (set_mset (to_mset expr\<^sub>1 + to_mset expr\<^sub>2)) (\<prec>) (\<prec>) (\<lambda>sub. sub \<cdot>\<^sub>s \<gamma>)"
      using grounding monotone_onI sub.ground_subst_stability
      by (metis (mono_tags, lifting) to_mset_to_set to_set_is_ground_subst union_iff)
  qed
qed

end

subsection \<open>Substitution update stability\<close>

locale subst_update_stable_multiset_extension =
  based_grounded_multiset_extension +
  sub: subst_update_stable_grounded_order where 
  vars = sub_vars and subst = sub_subst and to_ground = sub_to_ground and 
  from_ground = sub_from_ground
begin

(* TODO *)
no_notation less_eq (infix "\<preceq>" 50)

sublocale subst_update_stable_grounded_order where 
  less = "(\<prec>\<^sub>m)"  and vars = vars and subst = subst and from_ground = from_ground and 
  to_ground = to_ground
proof unfold_locales
  fix update x \<gamma> expr

  assume assms: 
    "base.is_ground update" "base_less update (\<gamma> x)" "is_ground (expr \<cdot> \<gamma>)" "x \<in> vars expr"

  moreover then have "\<forall>sub \<in># to_mset expr. sub \<cdot>\<^sub>s \<gamma>(x := update) \<preceq> sub \<cdot>\<^sub>s \<gamma>"
    using 
      sub.subst_update_stability
      sub.subst_reduntant_upd
      to_mset_to_set
      to_set_is_ground_subst
    by blast

  moreover have "\<exists>sub \<in># to_mset expr. sub \<cdot>\<^sub>s \<gamma>(x := update) \<prec> (sub \<cdot>\<^sub>s \<gamma>)"
    using sub.subst_update_stability assms
    unfolding vars_def subst_def to_mset_to_set
    by fastforce

  ultimately show "expr \<cdot> \<gamma>(x := update) \<prec>\<^sub>m expr \<cdot> \<gamma>"
    using all_less_eq_ex_less
    by blast
qed

end

end
