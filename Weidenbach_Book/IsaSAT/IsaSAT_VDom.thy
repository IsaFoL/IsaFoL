theory IsaSAT_VDom
  imports IsaSAT_Stats IsaSAT_Clauses
begin

paragraph \<open>AI-vdom\<close>
text \<open>
We keep all the indices. This is a subset of \<^term>\<open>vdom\<close> but is cleaned more aggressively.
At first we traid to express the relation directly but this was too cumbersome to use, due to having
both sets and multisets.
\<close>
type_synonym vdom = \<open>nat list\<close>
type_synonym aivdom = \<open>vdom \<times> vdom \<times> vdom\<close>
type_synonym isasat_aivdom = \<open>aivdom code_hider\<close>

abbreviation get_aivdom  :: \<open>isasat_aivdom \<Rightarrow> aivdom\<close> where
  \<open>get_aivdom \<equiv> get_content\<close>

abbreviation AIvdom :: \<open>aivdom \<Rightarrow> isasat_aivdom\<close> where
  \<open>AIvdom \<equiv> Constructor\<close>

fun get_vdom_aivdom where
  \<open>get_vdom_aivdom (AIvdom (vdom, avdom, ivdom)) = vdom\<close>

fun get_avdom_aivdom where
  \<open>get_avdom_aivdom (AIvdom (vdom, avdom, ivdom)) = avdom\<close>

fun get_ivdom_aivdom where
  \<open>get_ivdom_aivdom (AIvdom (vdom, avdom, ivdom)) = ivdom\<close>

fun aivdom_inv :: \<open>aivdom \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>aivdom_inv (vdom, avdom, ivdom) d \<longleftrightarrow>
    set avdom \<inter> set ivdom = {} \<and>
    set_mset d \<subseteq> set avdom \<union> set ivdom \<and>
    mset avdom \<subseteq># mset vdom \<and>
    mset ivdom \<subseteq># mset vdom \<and>
    distinct_mset d \<and>
    distinct vdom\<close>

definition aivdom_inv_dec :: \<open>isasat_aivdom \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>aivdom_inv_dec = aivdom_inv o get_aivdom\<close>

lemma aivdom_inv_alt_def:
  \<open>aivdom_inv (vdom, avdom, ivdom) d \<longleftrightarrow>
   (set avdom \<inter> set ivdom = {} \<and>
    set_mset d \<subseteq> set avdom \<union> set ivdom \<and>
    set avdom \<subseteq> set vdom \<and>
    set ivdom \<subseteq> set vdom \<and>
    distinct vdom\<and>
    distinct ivdom\<and>
    distinct_mset d \<and>
    distinct avdom)\<close>
  using distinct_mset_mono[of \<open>mset (avdom)\<close> \<open>mset (vdom)\<close>]
    distinct_mset_mono[of \<open>mset (ivdom)\<close> \<open>mset (vdom)\<close>]
    distinct_subseteq_iff[of  \<open>mset (avdom)\<close> \<open>mset (vdom)\<close>]
    distinct_subseteq_iff[of \<open>mset (ivdom)\<close> \<open>mset (vdom)\<close>]
  by auto

lemma AIvdom_split:
  \<open>aivdom = AIvdom (get_vdom_aivdom aivdom, get_avdom_aivdom aivdom, get_ivdom_aivdom aivdom)\<close>
  by (cases aivdom) auto


lemma aivdom_inv_dec_alt_def:
  \<open>aivdom_inv_dec aivdom d \<longleftrightarrow>
  (set (get_avdom_aivdom aivdom) \<inter> set (get_ivdom_aivdom aivdom) = {} \<and>
    set_mset d \<subseteq> set (get_avdom_aivdom aivdom) \<union> set (get_ivdom_aivdom aivdom) \<and>
    mset (get_avdom_aivdom aivdom) \<subseteq># mset (get_vdom_aivdom aivdom) \<and>
    mset (get_ivdom_aivdom aivdom) \<subseteq># mset (get_vdom_aivdom aivdom) \<and>
  distinct_mset d \<and> distinct (get_vdom_aivdom aivdom))\<close>
  apply (subst AIvdom_split)
  apply (subst aivdom_inv_dec_def)
  apply (subst comp_def)
  apply (simp add: aivdom_inv_alt_def)
  done

lemma aivdom_inv_dec_alt_def2:
  \<open>aivdom_inv_dec aivdom d \<longleftrightarrow>
  (set (get_avdom_aivdom aivdom) \<inter> set (get_ivdom_aivdom aivdom) = {} \<and>
    set_mset d \<subseteq> set (get_avdom_aivdom aivdom) \<union> set (get_ivdom_aivdom aivdom) \<and>
    mset (get_avdom_aivdom aivdom) \<subseteq># mset (get_vdom_aivdom aivdom) \<and>
    mset (get_ivdom_aivdom aivdom) \<subseteq># mset (get_vdom_aivdom aivdom) \<and>
  distinct_mset d \<and> distinct (get_vdom_aivdom aivdom) \<and> distinct (get_avdom_aivdom aivdom) \<and>
  distinct (get_ivdom_aivdom aivdom))\<close>
  apply (subst AIvdom_split)
  apply (subst aivdom_inv_dec_def)
  apply (subst comp_def)
  apply (auto dest: distinct_mset_mono simp add: aivdom_inv_alt_def)
  done
 
lemma distinct_butlast_set:
  \<open>distinct xs \<Longrightarrow> set (butlast xs) = set xs - {last xs}\<close>
  by (cases xs rule: rev_cases) auto

lemma distinct_remove_readd_last_set:
  \<open>distinct xs \<Longrightarrow> i < length xs \<Longrightarrow> set (butlast (xs[i := last xs])) = set xs - {xs!i}\<close>
  by (cases xs rule: rev_cases) (auto simp: list_update_append set_update_distinct nth_append)

definition add_learned_clause_aivdom_int where
  \<open>add_learned_clause_aivdom_int = (\<lambda> C (vdom, avdom, ivdom). (vdom @ [C], avdom @ [C], ivdom))\<close>

definition add_learned_clause_aivdom :: \<open>_ \<Rightarrow> isasat_aivdom \<Rightarrow> isasat_aivdom\<close> where
  \<open>add_learned_clause_aivdom C \<equiv> AIvdom o add_learned_clause_aivdom_int C o get_aivdom\<close>

lemma aivdom_inv_intro_add_mset:
  \<open>C \<notin># d \<Longrightarrow> C \<notin> set vdom \<Longrightarrow> aivdom_inv (vdom, avdom, ivdom) d \<Longrightarrow> aivdom_inv (vdom @ [C], avdom @ [C], ivdom) (add_mset C d)\<close>
  unfolding aivdom_inv_alt_def
  by (cases \<open>C \<in> (set (avdom) \<union> set (ivdom))\<close>)
   (auto dest: subset_mset_imp_subset_add_mset simp: add_learned_clause_aivdom_int_def split: code_hider.splits)

lemma aivdom_inv_dec_intro_add_mset:
  \<open>C \<notin># d \<Longrightarrow> C \<notin> set (get_vdom_aivdom aivdom) \<Longrightarrow> aivdom_inv_dec aivdom d \<Longrightarrow> aivdom_inv_dec (add_learned_clause_aivdom C aivdom) (add_mset C d)\<close>
  using aivdom_inv_intro_add_mset[of C d \<open>get_vdom_aivdom aivdom\<close> \<open>get_avdom_aivdom aivdom\<close>
    \<open>get_ivdom_aivdom aivdom\<close>]
  by (cases aivdom)
    (auto simp: aivdom_inv_dec_def add_learned_clause_aivdom_int_def add_learned_clause_aivdom_def
    simp del: aivdom_inv.simps)

definition remove_inactive_aivdom_int :: \<open>_ \<Rightarrow> aivdom \<Rightarrow> aivdom\<close> where
  \<open>remove_inactive_aivdom_int = (\<lambda>i (vdom, avdom, ivdom). (vdom, delete_index_and_swap avdom i, ivdom))\<close>

definition remove_inactive_aivdom :: \<open>_ \<Rightarrow> isasat_aivdom \<Rightarrow> isasat_aivdom\<close> where
  \<open>remove_inactive_aivdom C \<equiv> AIvdom o remove_inactive_aivdom_int C o get_aivdom\<close>

lemma aivdom_inv_remove_and_swap_inactive:
  assumes \<open>i < length n\<close> and \<open>aivdom_inv (m, n, s) baa\<close>
  shows \<open>aivdom_inv (m, butlast (n[i := last n]), s) (remove1_mset (n ! i) baa)\<close>
proof -
  have [simp]: \<open>set n - {n ! i} \<union> set s = set n \<union> set s - {n ! i}\<close>
    using assms nth_mem[of i n]
    by (auto simp: aivdom_inv_alt_def distinct_remove_readd_last_set
      dest: in_set_butlastD in_vdom_m_fmdropD simp del: nth_mem)
  have [simp]: \<open>mset_set (set n \<union> set s - {n ! i}) = remove1_mset (n!i) (mset_set (set n \<union> set s))\<close>
     using assms
     by (auto simp: aivdom_inv_alt_def mset_set_Diff)
  show ?thesis
    using assms distinct_mset_mono[of \<open>mset n\<close> \<open>mset m\<close>]
    by (auto simp: aivdom_inv_alt_def distinct_remove_readd_last_set mset_le_subtract distinct_butlast_set
       dest: in_set_butlastD in_vdom_m_fmdropD simp del: nth_mem)
qed
lemma aivdom_inv_dec_remove_and_swap_inactive:
  assumes \<open>i < length (get_avdom_aivdom ai)\<close> and \<open>aivdom_inv_dec ai baa\<close>
  shows \<open>aivdom_inv_dec (remove_inactive_aivdom i ai)  (remove1_mset (get_avdom_aivdom ai ! i) baa)\<close>
  using aivdom_inv_remove_and_swap_inactive[of i \<open>get_avdom_aivdom ai\<close>
    \<open>get_vdom_aivdom ai\<close> \<open>get_ivdom_aivdom ai\<close> baa] assms
  by (cases ai; auto simp: aivdom_inv_dec_def remove_inactive_aivdom_int_def remove_inactive_aivdom_def
    simp del: aivdom_inv.simps)

lemma aivdom_inv_remove_clause:
  \<open>aivdom_inv ai baa \<Longrightarrow> aivdom_inv ai (remove1_mset C baa)\<close>
  by (cases ai) (auto simp: aivdom_inv_alt_def distinct_remove_readd_last_set
      dest: in_set_butlastD dest: in_diffD)

lemma aivdom_inv_dec_remove_clause:
  \<open>aivdom_inv_dec ai baa \<Longrightarrow> aivdom_inv_dec ai (remove1_mset C baa)\<close>
  using aivdom_inv_remove_clause[of \<open>get_content ai\<close> baa]
  by (auto simp: aivdom_inv_dec_def)

lemma aivdom_inv_removed_inactive:
  assumes \<open>i < length n\<close> and \<open>aivdom_inv (m, n, s) baa\<close> \<open>n!i \<notin># baa\<close>
  shows \<open>aivdom_inv (m, butlast (n[i := last n]), s) baa\<close>
  by (metis aivdom_inv_remove_and_swap_inactive assms(1) assms(2) assms(3) diff_single_trivial)

lemma aivdom_inv_dec_removed_inactive:
  assumes \<open>i < length (get_avdom_aivdom ai)\<close> and \<open>aivdom_inv_dec ai baa\<close> \<open>get_avdom_aivdom ai!i \<notin># baa\<close>
  shows \<open>aivdom_inv_dec (remove_inactive_aivdom i ai) baa\<close>
  using aivdom_inv_removed_inactive[OF assms(1), of \<open>get_vdom_aivdom ai\<close>
    \<open>get_ivdom_aivdom ai\<close> baa] assms(2-)
  by (cases ai)
    (auto simp: aivdom_inv_dec_def remove_inactive_aivdom_int_def
    remove_inactive_aivdom_def simp del: aivdom_inv.simps)

(*TODO rename all*)
lemmas aivdom_inv_remove_and_swap_removed = aivdom_inv_removed_inactive


lemma get_aivdom_remove_inactive_aivdom[simp]:
  \<open>get_vdom_aivdom (remove_inactive_aivdom i m) = get_vdom_aivdom m\<close>
  \<open>get_avdom_aivdom (remove_inactive_aivdom i m) = (delete_index_and_swap (get_avdom_aivdom m) i)\<close>
  \<open>get_ivdom_aivdom (remove_inactive_aivdom i m) = get_ivdom_aivdom m\<close>
by (cases m; auto simp: remove_inactive_aivdom_def remove_inactive_aivdom_int_def; fail)+

end