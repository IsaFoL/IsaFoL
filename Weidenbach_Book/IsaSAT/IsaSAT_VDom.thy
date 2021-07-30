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
type_synonym aivdom = \<open>vdom \<times> vdom \<times> vdom \<times> vdom\<close>
type_synonym isasat_aivdom = \<open>aivdom code_hider\<close>

abbreviation get_aivdom  :: \<open>isasat_aivdom \<Rightarrow> aivdom\<close> where
  \<open>get_aivdom \<equiv> get_content\<close>

abbreviation AIvdom :: \<open>aivdom \<Rightarrow> isasat_aivdom\<close> where
  \<open>AIvdom \<equiv> Constructor\<close>

fun get_vdom_aivdom where
  \<open>get_vdom_aivdom (AIvdom (vdom, avdom, ivdom, tvdom)) = vdom\<close>

fun get_avdom_aivdom where
  \<open>get_avdom_aivdom (AIvdom (vdom, avdom, ivdom, tvdom)) = avdom\<close>

fun get_ivdom_aivdom where
  \<open>get_ivdom_aivdom (AIvdom (vdom, avdom, ivdom, tvdom)) = ivdom\<close>

fun get_tvdom_aivdom where
  \<open>get_tvdom_aivdom (AIvdom (vdom, avdom, ivdom, tvdom)) = tvdom\<close>

fun aivdom_inv :: \<open>aivdom \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>aivdom_inv (vdom, avdom, ivdom, tvdom) d \<longleftrightarrow>
    set avdom \<inter> set ivdom = {} \<and>
    set_mset d \<subseteq> set avdom \<union> set ivdom \<and>
    mset avdom \<subseteq># mset vdom \<and>
    mset ivdom \<subseteq># mset vdom \<and>
    distinct_mset d \<and>
    distinct vdom \<and>
    distinct tvdom \<and>
    mset tvdom \<subseteq># mset vdom\<close>

fun aivdom_inv_strong :: \<open>aivdom \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>aivdom_inv_strong (vdom, avdom, ivdom, tvdom) d \<longleftrightarrow>
    (aivdom_inv (vdom, avdom, ivdom, tvdom) d \<and> tvdom = vdom)\<close>

definition aivdom_inv_dec :: \<open>isasat_aivdom \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>aivdom_inv_dec = aivdom_inv o get_aivdom\<close>

definition aivdom_inv_strong_dec :: \<open>isasat_aivdom \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>aivdom_inv_strong_dec = aivdom_inv_strong o get_aivdom\<close>

lemma aivdom_inv_strong_dec_def2:
  \<open>aivdom_inv_strong_dec x a \<longleftrightarrow> aivdom_inv_dec x a \<and> get_vdom_aivdom x = get_tvdom_aivdom x\<close>
  by (cases x) (auto simp: aivdom_inv_strong_dec_def aivdom_inv_dec_def)

lemma aivdom_inv_alt_def:
  \<open>aivdom_inv (vdom, avdom, ivdom, tvdom) d \<longleftrightarrow>
   (set avdom \<inter> set ivdom = {} \<and>
    set_mset d \<subseteq> set avdom \<union> set ivdom \<and>
    set avdom \<subseteq> set vdom \<and>
    set ivdom \<subseteq> set vdom \<and>
    distinct vdom\<and>
    distinct ivdom\<and>
    distinct_mset d \<and>
    distinct avdom\<and>
    distinct tvdom \<and>
    set tvdom \<subseteq> set vdom)\<close>
  using distinct_mset_mono[of \<open>mset (avdom)\<close> \<open>mset (vdom)\<close>]
    distinct_mset_mono[of \<open>mset (ivdom)\<close> \<open>mset (vdom)\<close>]
    distinct_subseteq_iff[of  \<open>mset (avdom)\<close> \<open>mset (vdom)\<close>]
    distinct_subseteq_iff[of \<open>mset (ivdom)\<close> \<open>mset (vdom)\<close>]
    distinct_subseteq_iff[of \<open>mset (tvdom)\<close> \<open>mset (vdom)\<close>]
  by auto

lemma AIvdom_split:
  \<open>aivdom = AIvdom (get_vdom_aivdom aivdom, get_avdom_aivdom aivdom, get_ivdom_aivdom aivdom, get_tvdom_aivdom aivdom)\<close>
  by (cases aivdom) auto


lemma aivdom_inv_dec_alt_def:
  \<open>aivdom_inv_dec aivdom d \<longleftrightarrow>
  (set (get_avdom_aivdom aivdom) \<inter> set (get_ivdom_aivdom aivdom) = {} \<and>
    set_mset d \<subseteq> set (get_avdom_aivdom aivdom) \<union> set (get_ivdom_aivdom aivdom) \<and>
    mset (get_avdom_aivdom aivdom) \<subseteq># mset (get_vdom_aivdom aivdom) \<and>
    mset (get_ivdom_aivdom aivdom) \<subseteq># mset (get_vdom_aivdom aivdom) \<and>
  distinct_mset d \<and> distinct (get_vdom_aivdom aivdom) \<and>
  mset (get_tvdom_aivdom aivdom) \<subseteq># mset (get_vdom_aivdom aivdom)  \<and> distinct (get_tvdom_aivdom aivdom))\<close>
  apply (subst AIvdom_split)
  apply (subst aivdom_inv_dec_def)
  apply (subst comp_def)
  apply (auto simp add: aivdom_inv_alt_def)
  done

lemma aivdom_inv_dec_alt_def2:
  \<open>aivdom_inv_dec aivdom d \<longleftrightarrow>
  (set (get_avdom_aivdom aivdom) \<inter> set (get_ivdom_aivdom aivdom) = {} \<and>
    set_mset d \<subseteq> set (get_avdom_aivdom aivdom) \<union> set (get_ivdom_aivdom aivdom) \<and>
    mset (get_avdom_aivdom aivdom) \<subseteq># mset (get_vdom_aivdom aivdom) \<and>
    mset (get_ivdom_aivdom aivdom) \<subseteq># mset (get_vdom_aivdom aivdom) \<and>
  distinct_mset d \<and> distinct (get_vdom_aivdom aivdom) \<and> distinct (get_avdom_aivdom aivdom) \<and>
  distinct (get_ivdom_aivdom aivdom)\<and>
  mset (get_tvdom_aivdom aivdom) \<subseteq># mset (get_vdom_aivdom aivdom)  \<and> distinct (get_tvdom_aivdom aivdom))\<close>
  apply (subst AIvdom_split)
  apply (subst aivdom_inv_dec_def)
  apply (subst comp_def)
  apply (auto dest: distinct_mset_mono simp add: aivdom_inv_alt_def)
  done

lemmas aivdom_inv_strong_dec_alt_def =
  aivdom_inv_strong_dec_def2[unfolded aivdom_inv_dec_alt_def2]

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
  \<open>C \<notin># d \<Longrightarrow> C \<notin> set vdom \<Longrightarrow> aivdom_inv (vdom, avdom, ivdom, tvdom) d \<Longrightarrow> aivdom_inv (vdom @ [C], avdom @ [C], ivdom, tvdom) (add_mset C d)\<close>
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

definition add_init_clause_aivdom_int where
  \<open>add_init_clause_aivdom_int = (\<lambda> C (vdom, avdom, ivdom, tvdom). (vdom @ [C], avdom, ivdom @ [C], tvdom))\<close>

definition add_init_clause_aivdom :: \<open>_ \<Rightarrow> isasat_aivdom \<Rightarrow> isasat_aivdom\<close> where
  \<open>add_init_clause_aivdom C \<equiv> AIvdom o add_init_clause_aivdom_int C o get_aivdom\<close>

lemma aivdom_inv_intro_init_add_mset:
  \<open>C \<notin># d \<Longrightarrow> C \<notin> set vdom \<Longrightarrow> aivdom_inv (vdom, avdom, ivdom, tvdom) d \<Longrightarrow> aivdom_inv (vdom @ [C], avdom, ivdom @ [C], tvdom) (add_mset C d)\<close>
  unfolding aivdom_inv_alt_def
  by (cases \<open>C \<in> (set (avdom) \<union> set (ivdom))\<close>)
   (auto dest: subset_mset_imp_subset_add_mset simp: add_init_clause_aivdom_int_def split: code_hider.splits)

lemma aivdom_inv_dec_intro_init_add_mset:
  \<open>C \<notin># d \<Longrightarrow> C \<notin> set (get_vdom_aivdom aivdom) \<Longrightarrow> aivdom_inv_dec aivdom d \<Longrightarrow> aivdom_inv_dec (add_init_clause_aivdom C aivdom) (add_mset C d)\<close>
  using aivdom_inv_intro_init_add_mset[of C d \<open>get_vdom_aivdom aivdom\<close> \<open>get_avdom_aivdom aivdom\<close>
    \<open>get_ivdom_aivdom aivdom\<close> \<open>get_tvdom_aivdom aivdom\<close>]
  by (cases aivdom)
    (auto simp: aivdom_inv_dec_def add_init_clause_aivdom_int_def add_init_clause_aivdom_def
    simp del: aivdom_inv.simps)

definition remove_inactive_aivdom_int :: \<open>_ \<Rightarrow> aivdom \<Rightarrow> aivdom\<close> where
  \<open>remove_inactive_aivdom_int = (\<lambda>i (vdom, avdom, ivdom). (vdom, delete_index_and_swap avdom i, ivdom))\<close>

definition remove_inactive_aivdom :: \<open>_ \<Rightarrow> isasat_aivdom \<Rightarrow> isasat_aivdom\<close> where
  \<open>remove_inactive_aivdom C \<equiv> AIvdom o remove_inactive_aivdom_int C o get_aivdom\<close>

lemma aivdom_inv_remove_and_swap_inactive:
  assumes \<open>i < length n\<close> and \<open>aivdom_inv (m, n, s, tv) baa\<close>
  shows \<open>aivdom_inv (m, butlast (n[i := last n]), s, tv) (remove1_mset (n ! i) baa)\<close>
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
    \<open>get_vdom_aivdom ai\<close> \<open>get_ivdom_aivdom ai\<close> \<open>get_tvdom_aivdom ai\<close> baa] assms
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
  assumes \<open>i < length n\<close> and \<open>aivdom_inv (m, n, s, tv) baa\<close> \<open>n!i \<notin># baa\<close>
  shows \<open>aivdom_inv (m, butlast (n[i := last n]), s, tv) baa\<close>
  by (metis aivdom_inv_remove_and_swap_inactive assms(1) assms(2) assms(3) diff_single_trivial)

lemma aivdom_inv_dec_removed_inactive:
  assumes \<open>i < length (get_avdom_aivdom ai)\<close> and \<open>aivdom_inv_dec ai baa\<close> \<open>get_avdom_aivdom ai!i \<notin># baa\<close>
  shows \<open>aivdom_inv_dec (remove_inactive_aivdom i ai) baa\<close>
  using aivdom_inv_removed_inactive[OF assms(1), of \<open>get_vdom_aivdom ai\<close>
    \<open>get_ivdom_aivdom ai\<close> \<open>get_tvdom_aivdom ai\<close> baa] assms(2-)
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

definition vdom_aivdom_at_int :: \<open>aivdom \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>vdom_aivdom_at_int  = (\<lambda>(a,b,c) C. a ! C)\<close>

definition vdom_aivdom_at :: \<open>isasat_aivdom \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>vdom_aivdom_at ai C = get_vdom_aivdom ai ! C\<close>

lemma vdom_aivdom_at_alt_def:
  \<open>vdom_aivdom_at = vdom_aivdom_at_int o get_content\<close>
  by (intro ext, rename_tac x y, case_tac x) (auto simp: vdom_aivdom_at_int_def vdom_aivdom_at_def)


definition avdom_aivdom_at_int :: \<open>aivdom \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>avdom_aivdom_at_int = (\<lambda>(a,b,c) C. b ! C)\<close>

definition avdom_aivdom_at :: \<open>isasat_aivdom \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>avdom_aivdom_at ai C = get_avdom_aivdom ai ! C\<close>

lemma avdom_aivdom_at_alt_def:
  \<open>avdom_aivdom_at = avdom_aivdom_at_int o get_content\<close>
  by (intro ext, rename_tac x y, case_tac x) (auto simp: avdom_aivdom_at_int_def avdom_aivdom_at_def)


definition ivdom_aivdom_at_int :: \<open>aivdom \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>ivdom_aivdom_at_int = (\<lambda>(a,b,c,d) C. c ! C)\<close>

definition ivdom_aivdom_at :: \<open>isasat_aivdom \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>ivdom_aivdom_at ai C = get_ivdom_aivdom ai ! C\<close>

lemma ivdom_aivdom_at_alt_def:
  \<open>ivdom_aivdom_at = ivdom_aivdom_at_int o get_content\<close>
  by (intro ext, rename_tac x y, case_tac x) (auto simp: ivdom_aivdom_at_int_def ivdom_aivdom_at_def)

definition tvdom_aivdom_at_int :: \<open>aivdom \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>tvdom_aivdom_at_int = (\<lambda>(a,b,c,d) C. d ! C)\<close>

definition tvdom_aivdom_at :: \<open>isasat_aivdom \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>tvdom_aivdom_at ai C = get_tvdom_aivdom ai ! C\<close>

lemma tvdom_aivdom_at_alt_def:
  \<open>tvdom_aivdom_at = tvdom_aivdom_at_int o get_content\<close>
  by (intro ext, rename_tac x y, case_tac x) (auto simp: tvdom_aivdom_at_int_def tvdom_aivdom_at_def)

definition length_ivdom_aivdom_int :: \<open>aivdom \<Rightarrow> nat\<close> where
  \<open>length_ivdom_aivdom_int = (\<lambda>(a,b,c,d). length c)\<close>

definition length_ivdom_aivdom :: \<open>isasat_aivdom \<Rightarrow> nat\<close> where
  \<open>length_ivdom_aivdom ai = length (get_ivdom_aivdom ai)\<close>

lemma length_ivdom_aivdom_alt_def:
  \<open>length_ivdom_aivdom = length_ivdom_aivdom_int o get_content\<close>
  by (intro ext, rename_tac x, case_tac x) (auto simp: length_ivdom_aivdom_def length_ivdom_aivdom_int_def)

definition length_avdom_aivdom_int :: \<open>aivdom \<Rightarrow> nat\<close> where
  \<open>length_avdom_aivdom_int = (\<lambda>(a,b,c). length b)\<close>

definition length_avdom_aivdom :: \<open>isasat_aivdom \<Rightarrow> nat\<close> where
  \<open>length_avdom_aivdom ai = length (get_avdom_aivdom ai)\<close>

lemma length_avdom_aivdom_alt_def:
  \<open>length_avdom_aivdom = length_avdom_aivdom_int o get_content\<close>
  by (intro ext, rename_tac x, case_tac x) (auto simp: length_avdom_aivdom_def length_avdom_aivdom_int_def)

definition length_vdom_aivdom_int :: \<open>aivdom \<Rightarrow> nat\<close> where
  \<open>length_vdom_aivdom_int = (\<lambda>(a,b,c). length a)\<close>

definition length_vdom_aivdom :: \<open>isasat_aivdom \<Rightarrow> nat\<close> where
  \<open>length_vdom_aivdom ai = length (get_vdom_aivdom ai)\<close>

lemma length_vdom_aivdom_alt_def:
  \<open>length_vdom_aivdom = length_vdom_aivdom_int o get_content\<close>
  by (intro ext, rename_tac x, case_tac x) (auto simp: length_vdom_aivdom_def length_vdom_aivdom_int_def)

definition length_tvdom_aivdom_int :: \<open>aivdom \<Rightarrow> nat\<close> where
  \<open>length_tvdom_aivdom_int = (\<lambda>(a,b,c,d). length d)\<close>

definition length_tvdom_aivdom :: \<open>isasat_aivdom \<Rightarrow> nat\<close> where
  \<open>length_tvdom_aivdom ai = length (get_tvdom_aivdom ai)\<close>

lemma length_tvdom_aivdom_alt_def:
  \<open>length_tvdom_aivdom = length_tvdom_aivdom_int o get_content\<close>
  by (intro ext, rename_tac x, case_tac x) (auto simp: length_tvdom_aivdom_def length_tvdom_aivdom_int_def)


definition add_init_clause_aivdom_strong_int where
  \<open>add_init_clause_aivdom_strong_int = (\<lambda> C (vdom, avdom, ivdom, tvdom). (vdom @ [C], avdom, ivdom @ [C], tvdom @ [C]))\<close>

definition add_init_clause_aivdom_strong :: \<open>_ \<Rightarrow> isasat_aivdom \<Rightarrow> isasat_aivdom\<close> where
  \<open>add_init_clause_aivdom_strong C \<equiv> AIvdom o add_init_clause_aivdom_strong_int C o get_aivdom\<close>

lemma aivdom_inv_intro_init_strong_add_mset:
  \<open>C \<notin># d \<Longrightarrow> C \<notin> set vdom \<Longrightarrow> aivdom_inv_strong (vdom, avdom, ivdom, tvdom) d \<Longrightarrow> aivdom_inv_strong (vdom @ [C], avdom, ivdom @ [C], tvdom @ [C]) (add_mset C d)\<close>
  unfolding aivdom_inv_alt_def
  by (cases \<open>C \<in> (set (avdom) \<union> set (ivdom))\<close>)
    (auto dest: subset_mset_imp_subset_add_mset simp: add_init_clause_aivdom_strong_int_def
    split: code_hider.splits)

lemma aivdom_inv_dec_intro_init_strong_add_mset:
  \<open>C \<notin># d \<Longrightarrow> C \<notin> set (get_vdom_aivdom aivdom) \<Longrightarrow> aivdom_inv_strong_dec aivdom d \<Longrightarrow> aivdom_inv_strong_dec (add_init_clause_aivdom_strong C aivdom) (add_mset C d)\<close>
  using aivdom_inv_intro_init_strong_add_mset[of C d \<open>get_vdom_aivdom aivdom\<close> \<open>get_avdom_aivdom aivdom\<close>
    \<open>get_ivdom_aivdom aivdom\<close> \<open>get_tvdom_aivdom aivdom\<close>]
  by (cases aivdom)
    (auto simp: aivdom_inv_dec_def add_init_clause_aivdom_strong_int_def add_init_clause_aivdom_strong_def
    aivdom_inv_strong_dec_def
    simp del: aivdom_inv.simps)

definition add_learned_clause_aivdom_strong_int where
  \<open>add_learned_clause_aivdom_strong_int = (\<lambda> C (vdom, avdom, ivdom, tvdom). (vdom @ [C], avdom @ [C], ivdom, tvdom @ [C]))\<close>

definition add_learned_clause_aivdom_strong :: \<open>_ \<Rightarrow> isasat_aivdom \<Rightarrow> isasat_aivdom\<close> where
  \<open>add_learned_clause_aivdom_strong C \<equiv> AIvdom o add_learned_clause_aivdom_strong_int C o get_aivdom\<close>

lemma aivdom_inv_intro_learned_strong_add_mset:
  \<open>C \<notin># d \<Longrightarrow> C \<notin> set vdom \<Longrightarrow> aivdom_inv_strong (vdom, avdom, ivdom, tvdom) d \<Longrightarrow> aivdom_inv_strong (vdom @ [C], avdom @ [C], ivdom, tvdom @ [C]) (add_mset C d)\<close>
  unfolding aivdom_inv_alt_def
  by (cases \<open>C \<in> (set (avdom) \<union> set (ivdom))\<close>)
    (auto dest: subset_mset_imp_subset_add_mset simp: add_learned_clause_aivdom_strong_int_def
    split: code_hider.splits)

lemma aivdom_inv_dec_intro_learned_strong_add_mset:
  \<open>C \<notin># d \<Longrightarrow> C \<notin> set (get_vdom_aivdom aivdom) \<Longrightarrow> aivdom_inv_strong_dec aivdom d \<Longrightarrow> aivdom_inv_strong_dec (add_learned_clause_aivdom_strong C aivdom) (add_mset C d)\<close>
  using aivdom_inv_intro_learned_strong_add_mset[of C d \<open>get_vdom_aivdom aivdom\<close> \<open>get_avdom_aivdom aivdom\<close>
    \<open>get_ivdom_aivdom aivdom\<close> \<open>get_tvdom_aivdom aivdom\<close>]
  by (cases aivdom)
    (auto simp: aivdom_inv_dec_def add_learned_clause_aivdom_strong_int_def add_learned_clause_aivdom_strong_def
    aivdom_inv_strong_dec_def
    simp del: aivdom_inv.simps)

lemma [simp]:
  \<open>get_vdom_aivdom (add_learned_clause_aivdom C aivdom) = get_vdom_aivdom aivdom @ [C]\<close>
  \<open>get_avdom_aivdom (add_learned_clause_aivdom C aivdom) = get_avdom_aivdom aivdom @ [C]\<close>
  \<open>get_ivdom_aivdom (add_learned_clause_aivdom C aivdom) = get_ivdom_aivdom aivdom\<close>
  \<open>get_tvdom_aivdom (add_learned_clause_aivdom C aivdom) = get_tvdom_aivdom aivdom\<close>
  \<open>get_vdom_aivdom (add_init_clause_aivdom C aivdom) = get_vdom_aivdom aivdom @ [C]\<close>
  \<open>get_avdom_aivdom (add_init_clause_aivdom C aivdom) = get_avdom_aivdom aivdom\<close>
  \<open>get_ivdom_aivdom (add_init_clause_aivdom C aivdom) = get_ivdom_aivdom aivdom  @ [C]\<close>
  \<open>get_tvdom_aivdom (add_init_clause_aivdom C aivdom) = get_tvdom_aivdom aivdom\<close>
  \<open>get_vdom_aivdom (add_learned_clause_aivdom_strong C aivdom) = get_vdom_aivdom aivdom @ [C]\<close>
  \<open>get_avdom_aivdom (add_learned_clause_aivdom_strong C aivdom) = get_avdom_aivdom aivdom @ [C]\<close>
  \<open>get_ivdom_aivdom (add_learned_clause_aivdom_strong C aivdom) = get_ivdom_aivdom aivdom\<close>
  \<open>get_tvdom_aivdom (add_learned_clause_aivdom_strong C aivdom) = get_tvdom_aivdom aivdom @ [C]\<close>
  \<open>get_vdom_aivdom (add_init_clause_aivdom_strong C aivdom) = get_vdom_aivdom aivdom @ [C]\<close>
  \<open>get_avdom_aivdom (add_init_clause_aivdom_strong C aivdom) = get_avdom_aivdom aivdom\<close>
  \<open>get_ivdom_aivdom (add_init_clause_aivdom_strong C aivdom) = get_ivdom_aivdom aivdom  @ [C]\<close>
  \<open>get_tvdom_aivdom (add_init_clause_aivdom_strong C aivdom) = get_tvdom_aivdom aivdom @ [C]\<close>
  by (cases aivdom; auto simp: add_learned_clause_aivdom_def add_learned_clause_aivdom_int_def
    add_learned_clause_aivdom_strong_def add_learned_clause_aivdom_strong_int_def
    add_init_clause_aivdom_strong_def add_init_clause_aivdom_strong_int_def
    add_init_clause_aivdom_def add_init_clause_aivdom_int_def; fail)+

definition empty_aivdom_int where
  \<open>empty_aivdom_int = (\<lambda>(vdom, avdom, ivdom, tvdom). (take 0 vdom, take 0 avdom, take 0 ivdom, take 0 tvdom))\<close>

definition empty_aivdom :: \<open>isasat_aivdom \<Rightarrow> isasat_aivdom\<close> where
  \<open>empty_aivdom = Constructor o empty_aivdom_int o get_content\<close>

lemma [simp]:
  \<open>get_vdom_aivdom (empty_aivdom aivdom) = []\<close>
  \<open>get_avdom_aivdom (empty_aivdom aivdom) = []\<close>
  \<open>get_ivdom_aivdom (empty_aivdom aivdom) = []\<close>
  \<open>get_tvdom_aivdom (empty_aivdom aivdom) = []\<close>
  \<open>aivdom_inv_dec (empty_aivdom aivdom) {#}\<close>
  \<open>aivdom_inv_strong_dec (empty_aivdom aivdom) {#}\<close>
  by (auto simp: empty_aivdom_def empty_aivdom_int_def aivdom_inv_dec_alt_def
    aivdom_inv_strong_dec_def)

fun swap_avdom_aivdom where
  \<open>swap_avdom_aivdom (AIvdom (vdom, avdom, ivdom, tvdom)) i j =
  (AIvdom (vdom, swap avdom i j, ivdom, tvdom))\<close>

lemma [simp]:
  \<open>get_avdom_aivdom (swap_avdom_aivdom aivdom i j) = swap (get_avdom_aivdom aivdom) i j\<close>
  \<open>get_vdom_aivdom (swap_avdom_aivdom aivdom i j) = (get_vdom_aivdom aivdom)\<close>
  \<open>get_ivdom_aivdom (swap_avdom_aivdom aivdom i j) = (get_ivdom_aivdom aivdom)\<close>
  \<open>get_tvdom_aivdom (swap_avdom_aivdom aivdom i j) = (get_tvdom_aivdom aivdom)\<close>
  by (cases aivdom; auto simp:)+

fun take_avdom_aivdom where
  \<open>take_avdom_aivdom i (AIvdom (vdom, avdom, ivdom, tvdom)) =
  (AIvdom (vdom, take i avdom, ivdom, tvdom))\<close>

lemma [simp]:
  \<open>get_avdom_aivdom (take_avdom_aivdom i aivdom) = take i (get_avdom_aivdom aivdom)\<close>
  \<open>get_vdom_aivdom (take_avdom_aivdom i aivdom) = get_vdom_aivdom aivdom\<close>
  \<open>get_tvdom_aivdom (take_avdom_aivdom i aivdom) = get_tvdom_aivdom aivdom\<close>
  \<open>get_ivdom_aivdom (take_avdom_aivdom i aivdom) = get_ivdom_aivdom aivdom\<close>
  by (cases aivdom; auto simp:; fail)+

definition map_vdom_aivdom :: \<open>_\<close> where
  \<open>map_vdom_aivdom f = (\<lambda>x. case x of AIvdom (vdom, avdom, ivdom, tvdom) \<Rightarrow> do {
    avdom \<leftarrow> f avdom;
    RETURN (AIvdom (vdom, avdom, ivdom, tvdom))
  })\<close>

definition AIvdom_init :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> isasat_aivdom\<close> where
  \<open>AIvdom_init vdom avdom ivdom = AIvdom (vdom, avdom, ivdom, vdom)\<close>


definition push_to_tvdom_int where
  \<open>push_to_tvdom_int = (\<lambda> C (vdom, avdom, ivdom, tvdom). (vdom, avdom, ivdom, tvdom @ [C]))\<close>

definition push_to_tvdom :: \<open>_ \<Rightarrow> isasat_aivdom \<Rightarrow> isasat_aivdom\<close> where
  \<open>push_to_tvdom C \<equiv> AIvdom o push_to_tvdom_int C o get_aivdom\<close>

lemma aivdom_inv_push_to_tvdom_int:
  \<open>C \<in> set vdom \<Longrightarrow> C \<notin> set tvdom \<Longrightarrow> aivdom_inv (vdom, avdom, ivdom, tvdom) d \<Longrightarrow> aivdom_inv (vdom, avdom, ivdom, tvdom @ [C]) d\<close>
  unfolding aivdom_inv_alt_def
  by (auto dest: subset_mset_imp_subset_add_mset simp: add_learned_clause_aivdom_strong_int_def
    split: code_hider.splits)

lemma \<open>C \<in> set (get_vdom_aivdom aivdom) \<Longrightarrow> C \<notin> set (get_tvdom_aivdom aivdom) \<Longrightarrow> aivdom_inv_dec aivdom d \<Longrightarrow> aivdom_inv_dec (push_to_tvdom C aivdom) d\<close>
  using aivdom_inv_push_to_tvdom_int[of C \<open>get_vdom_aivdom aivdom\<close> \<open>get_tvdom_aivdom aivdom\<close>
    \<open>get_avdom_aivdom aivdom\<close> \<open>get_ivdom_aivdom aivdom\<close> d]
  by (cases aivdom)
    (auto simp: aivdom_inv_dec_def add_learned_clause_aivdom_strong_int_def add_learned_clause_aivdom_strong_def
    aivdom_inv_strong_dec_def push_to_tvdom_def push_to_tvdom_int_def
    simp del: aivdom_inv.simps)

end