theory CDCL_Two_Watched_Literals_VMTF
imports CDCL_Two_Watched_Literals_List_Watched_Code_Common
begin

type_synonym 'v abs_vmtf = \<open>'v set \<times> 'v set\<close>
type_synonym 'v abs_vmtf_remove = \<open>'v abs_vmtf \<times> 'v set\<close>

subsection \<open>Variable-Move-to-Front\<close>

subsubsection \<open>Specification\<close>

context twl_array_code_ops
begin

paragraph \<open>Invariants\<close>

text \<open>Invariants
  \<^item> The atoms are always disjoint.
  \<^item> The atoms of \<^term>\<open>ys\<close> are \<^emph>\<open>always\<close> set.
  \<^item> The atoms of \<^term>\<open>zs\<close> are \<^emph>\<open>never\<close> set and have been remove from \<^term>\<open>xs\<close> and \<^term>\<open>ys\<close>.
  \<^item> The atoms of \<^term>\<open>xs\<close> \<^emph>\<open>can be\<close> set but do not have to.
\<close>

definition abs_vmtf_remove_inv :: \<open>(nat, nat) ann_lits \<Rightarrow> nat abs_vmtf_remove \<Rightarrow> bool\<close> where
\<open>abs_vmtf_remove_inv M \<equiv> \<lambda>((xs, ys), zs).
  (\<forall>L\<in>ys. L \<in> atm_of ` lits_of_l M) \<and>
  xs \<inter> ys = {} \<and>
  xs \<inter> zs = {} \<and>
  ys \<inter> zs = {} \<and>
  xs \<union> ys \<union> zs = atms_of N\<^sub>1 \<and>
  (\<forall>L\<in>zs. L \<in> atm_of ` lits_of_l M) \<and>
  finite xs \<and> finite ys \<and> finite zs
  \<close>

abbreviation abs_vmtf_inv :: \<open>(nat, nat) ann_lits \<Rightarrow> nat abs_vmtf \<Rightarrow> bool\<close> where
\<open>abs_vmtf_inv M vm \<equiv> abs_vmtf_remove_inv M (vm, {})\<close>


paragraph \<open>Operations\<close>

fun abs_vmtf_bump :: \<open>nat literal \<Rightarrow> nat abs_vmtf_remove \<Rightarrow> nat abs_vmtf_remove\<close> where [simp del]:
\<open>abs_vmtf_bump L ((xs, ys), zs) = ((xs - {atm_of L}, ys - {atm_of L}), insert (atm_of L) zs)\<close>

fun abs_vmtf_bump_flush :: \<open>nat abs_vmtf_remove \<Rightarrow> nat abs_vmtf_remove\<close> where [simp del]:
\<open>abs_vmtf_bump_flush ((xs, ys), zs) = ((xs, ys \<union> zs), {})\<close>

lemmas abs_vmtf_bump_flush_def = abs_vmtf_bump_flush.simps
lemmas abs_vmtf_bump_def = abs_vmtf_bump.simps


lemma abs_vmtf_remove_inv_abs_vmtf_bump:
  assumes \<open>L \<in># N\<^sub>1\<close> and \<open>abs_vmtf_remove_inv M vm\<close> and \<open>defined_lit M L\<close>
  shows \<open>abs_vmtf_remove_inv M (abs_vmtf_bump L vm)\<close>
  using assms by (fastforce simp: abs_vmtf_remove_inv_def abs_vmtf_bump_def Decided_Propagated_in_iff_in_lits_of_l 
    in_N\<^sub>1_atm_of_in_atms_of_iff atm_of_eq_atm_of lits_of_def uminus_lit_swap)

lemma abs_vmtf_remove_inv_abs_vmtf_bump_flush:
  assumes \<open>abs_vmtf_remove_inv M vm\<close>
  shows \<open>abs_vmtf_remove_inv M (abs_vmtf_bump_flush vm)\<close>
  using assms by (auto simp: abs_vmtf_remove_inv_def abs_vmtf_bump_flush_def Decided_Propagated_in_iff_in_lits_of_l 
    in_N\<^sub>1_atm_of_in_atms_of_iff atm_of_eq_atm_of)


definition abs_vmtf_unset :: \<open>nat literal \<Rightarrow> nat abs_vmtf \<Rightarrow> nat abs_vmtf nres\<close> where
\<open>abs_vmtf_unset L \<equiv> \<lambda>(xs, ys). do {
    if atm_of L \<in> ys
    then do {
        ys' \<leftarrow> SPEC (\<lambda>ys'. ys' \<subseteq> ys \<and> atm_of L \<in> ys');
        RETURN (xs \<union> ys', ys-ys')
    }
    else RETURN (xs, ys)
  }\<close>

lemma abs_vmtf_remove_inv_abs_vmtf_unset:
  assumes \<open>abs_vmtf_inv M vm\<close> and \<open>undefined_lit M L\<close>
  shows \<open>abs_vmtf_unset L vm \<le> SPEC (abs_vmtf_inv M)\<close>
  using assms unfolding abs_vmtf_unset_def
  apply (cases vm)
  apply clarify
  apply refine_vcg
  by (fastforce simp: abs_vmtf_remove_inv_def abs_vmtf_bump_def Decided_Propagated_in_iff_in_lits_of_l 
    in_N\<^sub>1_atm_of_in_atms_of_iff atm_of_eq_atm_of lits_of_def uminus_lit_swap)

definition abs_vmtf_find_next :: \<open>(nat, nat) ann_lits \<Rightarrow> nat abs_vmtf \<Rightarrow> (nat option \<times> nat abs_vmtf) nres\<close> where
\<open>abs_vmtf_find_next M vm = do {
    WHILE\<^sub>T\<^bsup>\<lambda>(L, vm). 
       (L = None \<longrightarrow> abs_vmtf_inv M vm) \<and>
       (L \<noteq> None \<longrightarrow> (abs_vmtf_inv (Decided (Pos (the L)) # M) vm \<and> undefined_lit M (Pos (the L))))\<^esup>
      (\<lambda>(x, (xs, ys)). x = None \<and> xs \<noteq> {})
      (\<lambda>(x, (xs, ys)). do {
          ASSERT(xs \<noteq> {});
          x \<leftarrow> SPEC(\<lambda>x. x \<in> xs);
          if undefined_lit M (Pos x) then RETURN (Some x, (xs - {x}, insert x ys))
          else RETURN (None, (xs - {x}, insert x ys))
      })
      (None, vm)
  }\<close>

lemma abs_vmtf_remove_inv_abs_vmtf_find_next:
  assumes \<open>abs_vmtf_inv M vm\<close>
  shows \<open>abs_vmtf_find_next M vm \<le> SPEC (\<lambda>(L, vm).  
      (L = None \<longrightarrow> (abs_vmtf_inv M vm \<and> (\<forall>L\<in>#N\<^sub>1. defined_lit M L))) \<and>
      (L \<noteq> None \<longrightarrow> (abs_vmtf_inv (Decided (Pos (the L)) # M) vm \<and> undefined_lit M (Pos (the L)))))\<close>
proof -
  have body_defined_abs: \<open>abs_vmtf_inv M' vm'\<close>
    if  \<open>abs_vmtf_inv M vm\<close> and \<open>M' = M\<close> and
        \<open>vm' = (xs - {L}, insert L ys)\<close> and
        \<open>vm = (xs, ys)\<close> and
        def_L: \<open>\<not>undefined_lit M (Pos L)\<close> and
        \<open>L \<in> xs\<close>
    for vm vm' xs ys M M' L
    proof -
        have \<open>L \<in> atm_of ` lits_of_l M\<close>
        using def_L by (metis (full_types) Decided_Propagated_in_iff_in_lits_of_l atm_of_uminus 
            image_iff literal.sel(1))
        then show ?thesis
        using that by (auto simp: abs_vmtf_remove_inv_def)
    qed
  show ?thesis
    using assms unfolding abs_vmtf_find_next_def
    apply (cases vm)
    apply clarify
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(x, (xs, ys)). card xs)\<close>])
    subgoal by auto -- \<open>well-foundedness\<close>
    subgoal by auto -- \<open>WHILE inital round\<close>
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by (auto simp: abs_vmtf_remove_inv_def) -- \<open>body if undefined\<close>
    subgoal by (auto simp: abs_vmtf_remove_inv_def)
    subgoal by auto
    subgoal by (simp add:  abs_vmtf_remove_inv_def abs_vmtf_remove_inv_def card_Diff1_less
        del: card_Diff_singleton card_Diff_subset card_Diff_singleton card_Diff_insert) -- \<open>Termination\<close>
    subgoal by (rule body_defined_abs) simp_all+ -- \<open>body if defined\<close>
    subgoal by (auto simp: abs_vmtf_remove_inv_def)
    subgoal by (auto simp: abs_vmtf_remove_inv_def)
    subgoal by (simp add:  abs_vmtf_remove_inv_def abs_vmtf_remove_inv_def card_Diff1_less
        del: card_Diff_singleton card_Diff_subset card_Diff_singleton card_Diff_insert)-- \<open>Termination\<close>
    subgoal by (auto simp: abs_vmtf_remove_inv_def) --\<open>final theorem\<close>
    subgoal by (auto simp: abs_vmtf_remove_inv_def Decided_Propagated_in_iff_in_lits_of_l 
        atm_of_in_atm_of_set_in_uminus atms_of_def dest!: atm_of_in_atm_of_set_in_uminus)
    subgoal by fast
    subgoal by fast
    done
qed

lemma abs_vmtf_remove_inv_change_hd:
  assumes \<open>atm_of (lit_of L) = atm_of (lit_of L')\<close>
  shows \<open>abs_vmtf_remove_inv (L # M) (vm, {}) \<longleftrightarrow> abs_vmtf_remove_inv (L' # M) (vm, {})\<close>
  using assms by (auto simp: abs_vmtf_remove_inv_def)

end


subsubsection \<open>Implementation\<close>

end