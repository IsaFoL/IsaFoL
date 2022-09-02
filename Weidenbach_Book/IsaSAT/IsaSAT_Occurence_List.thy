theory IsaSAT_Occurence_List
  imports IsaSAT_Literals IsaSAT_Watch_List IsaSAT_Mark
begin

section \<open>Occurrence lists\<close>

text \<open>

Occurrence lists (in a single watched way) are very similar to watch lists. For simplification
purpose, we use occurrence lists and watch lists, but Kissat uses only the latter for memory
efficiency.

This file started as an experiment. We attempted to do better than our watch lists because we know
and understand a lot more on refinement. This turned out to do really work out as expected however.

There are two ways to achieve the refinement:

  \<^item> the most abstract requires to know the set of variable. Which means that we have to somehow get
it. Which is impossible (some of the information is deleted anyway), but also something we probably
should not try to do.

 \<^item> just use a bound.

What is the conclusion of all that? Well not much, except that full abstraction is hard to get. So
we still end up with the concrete data in the isasat state, which I find sad, but I don't see any
way to do it better -- and no I am no going back to a locale with an upper bound on the literals;
been there, done that.

\<close>

subsection \<open>Abstract Occurrence Lists\<close>

type_synonym raw_occurences = \<open>nat literal \<Rightarrow> nat list\<close>
type_synonym occurences = \<open>nat set \<times> raw_occurences\<close>

definition valid_occurrences where
  \<open>valid_occurrences \<B> = (\<lambda>(\<A>, xs). set_mset \<B> = \<A>)\<close>

text \<open>Only useful for proofs.\<close>
definition occ_list :: \<open>occurences \<Rightarrow> nat literal \<Rightarrow> nat list\<close> where
  \<open>occ_list = (\<lambda>(\<A>, xs) L. xs L)\<close>

definition occ_list_at :: \<open>occurences \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>occ_list_at \<A>xs L i = occ_list \<A>xs L ! i\<close>

definition occ_list_at_pre :: \<open>occurences \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>occ_list_at_pre = (\<lambda>(n, xs) L i. atm_of L \<in> n \<and> i < length (xs L))\<close>

definition mop_occ_list_at :: \<open>occurences \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
  \<open>mop_occ_list_at = (\<lambda>\<A>xs L i. do {
     ASSERT (occ_list_at_pre \<A>xs L i);
     RETURN (occ_list_at \<A>xs L i)
  })\<close>

definition occ_list_length_pre :: \<open>occurences \<Rightarrow> nat literal \<Rightarrow> bool\<close> where
  \<open>occ_list_length_pre = (\<lambda>(\<A>, xs) L. atm_of L \<in> \<A>)\<close>

definition occ_list_length :: \<open>occurences \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>occ_list_length = (\<lambda>(\<A>, xs) L. do {
      (length (xs L))
  })\<close>

definition mop_occ_list_length :: \<open>occurences \<Rightarrow> nat literal \<Rightarrow> nat nres\<close> where
  \<open>mop_occ_list_length = (\<lambda>\<A>xs L. do {
     ASSERT (occ_list_length_pre \<A>xs L);
     RETURN (occ_list_length \<A>xs L)
  })\<close>

definition occ_list_append_pre :: \<open>occurences \<Rightarrow> nat literal \<Rightarrow> bool\<close> where
  \<open>occ_list_append_pre = (\<lambda>(\<A>, xs) L. atm_of L \<in> \<A>)\<close>

definition occ_list_append :: \<open>nat \<Rightarrow> occurences \<Rightarrow> nat literal \<Rightarrow> occurences\<close> where
  \<open>occ_list_append = (\<lambda>x (\<A>, xs) L. (\<A>, xs (L := xs L @ [x])))\<close>

definition mop_occ_list_append :: \<open>nat \<Rightarrow> occurences \<Rightarrow> nat literal \<Rightarrow> occurences nres\<close> where
  \<open>mop_occ_list_append = (\<lambda>x \<A>xs L . do {
     ASSERT (occ_list_append_pre (\<A>xs) L);
     RETURN (occ_list_append x (\<A>xs) L)
  })\<close>


definition occ_list_clear_at_pre :: \<open>occurences \<Rightarrow> nat literal \<Rightarrow> bool\<close> where
  \<open>occ_list_clear_at_pre = (\<lambda>(\<A>, xs) L. atm_of L \<in> \<A>)\<close>

definition occ_list_clear_at :: \<open>occurences \<Rightarrow> nat literal \<Rightarrow> occurences nres\<close> where
  \<open>occ_list_clear_at = (\<lambda>(\<A>, xs) L . do {
     ASSERT (occ_list_clear_at_pre (\<A>, xs) L);
     RETURN (\<A>, xs (L := []))
  })\<close>

definition occ_list_clear_all_pre :: \<open>occurences \<Rightarrow> bool\<close> where
  \<open>occ_list_clear_all_pre = (\<lambda>(\<A>, xs). True)\<close>

definition occ_list_clear_all :: \<open>occurences \<Rightarrow> occurences nres\<close> where
  \<open>occ_list_clear_all = (\<lambda>(\<A>, xs) . do {
     ASSERT (occ_list_clear_all_pre (\<A>, xs));
     RETURN (\<A>, \<lambda>_. [])
  })\<close>

definition all_occurrences :: \<open>nat multiset \<Rightarrow> occurences \<Rightarrow> nat multiset\<close> where
  \<open>all_occurrences \<A> = (\<lambda>(n, xs). \<Sum>\<^sub># (mset `# xs `# Pos `# remdups_mset \<A> +
     mset `# xs `# Neg `# remdups_mset \<A>))\<close>

definition occ_list_create_pre :: \<open>nat set \<Rightarrow> nat set \<Rightarrow> bool\<close> where
  \<open>occ_list_create_pre n = (\<lambda>\<A>. True)\<close>

definition mop_occ_list_create :: \<open>nat set \<Rightarrow> occurences nres\<close> where
  \<open>mop_occ_list_create = (\<lambda>n. do {
     ASSERT (finite n);
     RETURN (n, \<lambda>_. [])
  })\<close>


abbreviation raw_empty_occs_list :: \<open>nat literal \<Rightarrow> nat list\<close> where
  \<open>raw_empty_occs_list \<equiv> (\<lambda>_. [])\<close>

definition empty_occs_list :: \<open>nat multiset \<Rightarrow> nat set \<times> (nat literal \<Rightarrow> nat list)\<close> where
  \<open>empty_occs_list \<A> \<equiv> (set_mset \<A>, \<lambda>_. [])\<close>

lemma empty_occs_list_cong:
  \<open>set_mset A = set_mset B \<Longrightarrow> empty_occs_list A = empty_occs_list B\<close>
  unfolding empty_occs_list_def by auto


definition occurrence_list where
  \<open>occurrence_list \<A> = {((n, ys), xs). (ys, xs)\<in>Id \<and> n = (set_mset \<A>)}\<close>

lemma mop_occ_list_create:
  shows \<open>mop_occ_list_create (set_mset \<A>) \<le> SPEC (\<lambda>c. (c, raw_empty_occs_list) \<in> occurrence_list \<A>)\<close> (is \<open>?A \<le> ?B\<close>)
  unfolding mop_occ_list_create_def
  by refine_vcg
    (use in \<open>auto simp:  RETURN_RES_refine_iff occurrence_list_def\<close>)

lemma mop_occ_list_at:
  assumes \<open>occ_list_at_pre occs L i\<close>
  shows \<open>mop_occ_list_at occs L i \<le> SPEC (\<lambda>c. (c, occ_list_at occs L i) \<in> Id)\<close> (is \<open>?A \<le> ?B\<close>)
  using assms unfolding mop_occ_list_at_def
  by refine_vcg auto

lemma mop_occ_list_append:
  assumes \<open>occ_list_append_pre occs L\<close>
  shows \<open>mop_occ_list_append x occs L \<le> SPEC (\<lambda>c. (c, occ_list_append x occs L) \<in> Id)\<close>
  using assms unfolding mop_occ_list_append_def
  by refine_vcg auto

abbreviation occ_list_append_r :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> (nat literal \<Rightarrow> nat list) \<Rightarrow> _\<close> where
  \<open>occ_list_append_r L x xs \<equiv> xs (L := xs L @ [x])\<close>


subsection \<open>Concrete Occurrence lists\<close>

text \<open>We use \<^text>\<open>cocc\<close> for concrete occurrence lists.\<close>

type_synonym occurences_ref = \<open>nat list list\<close>

abbreviation D\<^sub>1 :: \<open>nat set \<Rightarrow> (nat \<times> nat literal) set\<close> where
  \<open>D\<^sub>1 \<A>\<^sub>i\<^sub>n \<equiv> (\<lambda>L. (nat_of_lit L, L)) ` (Pos ` \<A>\<^sub>i\<^sub>n \<union> Neg ` \<A>\<^sub>i\<^sub>n)\<close>

definition occurrence_list_ref :: \<open>(occurences_ref \<times> occurences) set\<close> where
  \<open>occurrence_list_ref \<equiv> {(xs, (n, ys)). (xs, ys)\<in>\<langle>\<langle>nat_rel\<rangle>list_rel\<rangle>map_fun_rel (D\<^sub>1 n) \<and> (\<forall>L. L \<notin> fst ` (D\<^sub>1 n) \<longrightarrow> L < length xs \<longrightarrow> xs ! L = [])}\<close>

lemma empty_occs_list_cong':
  \<open>set_mset A = set_mset B \<Longrightarrow> (occs, empty_occs_list A) \<in> occurrence_list_ref \<Longrightarrow> (occs, empty_occs_list B) \<in> occurrence_list_ref\<close>
  unfolding empty_occs_list_def by auto

definition cocc_list_at :: \<open>occurences_ref \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>cocc_list_at xs L i = xs ! nat_of_lit L ! i\<close>


definition cocc_list_at_pre :: \<open>occurences_ref \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>cocc_list_at_pre = (\<lambda>xs L i. i < length (xs ! nat_of_lit L))\<close>

definition mop_cocc_list_at :: \<open>occurences_ref \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
  \<open>mop_cocc_list_at = (\<lambda>\<A>xs L i. do {
     ASSERT (cocc_list_at_pre \<A>xs L i);
     RETURN (cocc_list_at \<A>xs L i)
  })\<close>

(*TODO this is certainly a dup*)
lemma \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset:
  \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (add_mset K A)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l A) \<union> {Pos K, Neg K}\<close>
  by (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def)


lemma mop_cocc_list_at_mop_occ_list_at:
  assumes
    \<open>(xs, \<A>xs) \<in> occurrence_list_ref\<close>
    \<open>(L,L')\<in>Id\<close>
    \<open>(i,i')\<in>nat_rel\<close>
  shows
    \<open>mop_cocc_list_at xs L i \<le> \<Down>{(K,K'). (K,K')\<in>nat_rel \<and> K = occ_list_at \<A>xs L' i \<and> K = cocc_list_at xs L' i \<and> nat_of_lit L' < length xs \<and> i < length (xs ! nat_of_lit L)} (mop_occ_list_at \<A>xs L' i')\<close>
  using assms unfolding mop_cocc_list_at_def mop_occ_list_at_def occurrence_list_ref_def
  apply refine_rcg
  subgoal
    by (cases L)
     (auto simp: cocc_list_at_pre_def occ_list_at_pre_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset
      map_fun_rel_def dest: bspec[of _ _ L])
  subgoal
    by (cases L)
     (auto simp: cocc_list_at_pre_def occ_list_at_pre_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset cocc_list_at_def occ_list_at_def
        map_fun_rel_def occ_list_def dest: bspec[of _ _ L])
  done


definition cocc_list_length_pre :: \<open>occurences_ref \<Rightarrow> nat literal \<Rightarrow> bool\<close> where
  \<open>cocc_list_length_pre = (\<lambda>(xs) L. nat_of_lit L < length xs)\<close>

definition cocc_list_length :: \<open>occurences_ref \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>cocc_list_length = (\<lambda>xs L. do {
      (length (xs ! nat_of_lit L))
  })\<close>

definition mop_cocc_list_length :: \<open>occurences_ref \<Rightarrow> nat literal \<Rightarrow> nat nres\<close> where
  \<open>mop_cocc_list_length = (\<lambda>\<A>xs L. do {
     ASSERT (cocc_list_length_pre \<A>xs L);
     RETURN (cocc_list_length \<A>xs L)
  })\<close>


lemma mop_cocc_list_length_mop_occ_list_length:
  assumes
    \<open>(xs, \<A>xs) \<in> occurrence_list_ref\<close>
    \<open>(L,L')\<in>Id\<close>
  shows
    \<open>mop_cocc_list_length xs L \<le> \<Down>nat_rel (mop_occ_list_length \<A>xs L')\<close>
  using assms
  unfolding mop_cocc_list_length_def mop_occ_list_length_def occurrence_list_ref_def
  apply refine_vcg
  subgoal
    by (cases L)
     (auto simp: occ_list_length_pre_def cocc_list_length_pre_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset
        map_fun_rel_def dest!: multi_member_split)
  subgoal
    by (cases L)
     (auto simp: occ_list_length_pre_def cocc_list_length_pre_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset
        map_fun_rel_def occ_list_length_def cocc_list_length_def dest: bspec[of _ _ L])
   done

definition cocc_list_append_pre :: \<open>occurences_ref \<Rightarrow> nat literal \<Rightarrow> bool\<close> where
  \<open>cocc_list_append_pre = (\<lambda>xs L. nat_of_lit L < length xs)\<close>

definition cocc_list_append :: \<open>nat \<Rightarrow> occurences_ref \<Rightarrow> nat literal \<Rightarrow> occurences_ref\<close> where
  \<open>cocc_list_append = (\<lambda>x xs L. xs [nat_of_lit L := xs ! (nat_of_lit L) @ [x]])\<close>

definition mop_cocc_list_append :: \<open>nat \<Rightarrow> occurences_ref \<Rightarrow> nat literal \<Rightarrow> occurences_ref nres\<close> where
  \<open>mop_cocc_list_append = (\<lambda>x \<A>xs L . do {
     ASSERT (cocc_list_append_pre (\<A>xs) L);
     RETURN (cocc_list_append x (\<A>xs) L)
  })\<close>

lemma mop_cocc_list_append_mop_occ_list_append:
  assumes
    \<open>(xs, \<A>xs) \<in> occurrence_list_ref\<close>
    \<open>(L,L')\<in>Id\<close> and
    \<open>(x,x')\<in>nat_rel\<close>
  shows
    \<open>mop_cocc_list_append x xs L \<le> \<Down>{(a,b). (a,b)\<in>occurrence_list_ref \<and> a = cocc_list_append x xs L \<and> nat_of_lit L < length xs} (mop_occ_list_append x' \<A>xs L')\<close>
  using assms
  unfolding mop_cocc_list_append_def mop_occ_list_append_def occurrence_list_ref_def
  apply refine_vcg
  subgoal
    by (cases L)
     (auto simp: cocc_list_append_pre_def occ_list_append_pre_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset
        map_fun_rel_def  dest!: bspec[of _ _ L])
  subgoal
    apply (cases L)
    apply (auto simp: cocc_list_append_pre_def occ_list_append_pre_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset
        map_fun_rel_def cocc_list_append_def occ_list_append_def)
    apply (force simp add: image_image image_Un)+
    done
  done

definition mop_cocc_list_create :: \<open>nat \<Rightarrow> occurences_ref nres\<close> where
  \<open>mop_cocc_list_create = (\<lambda>n. do {
     RETURN (replicate n [])
  })\<close>

lemma mop_cocc_list_create_mop_occ_list_create:
  assumes \<open>n > 2* Max \<A> + 1\<close> \<open>finite \<A>\<close>
  shows \<open>mop_cocc_list_create n \<le> \<Down>(occurrence_list_ref) (mop_occ_list_create \<A>)\<close>
  unfolding mop_cocc_list_create_def mop_occ_list_create_def occurrence_list_ref_def
  using assms
  by (auto simp: map_fun_rel_def Max_gr_iff dest: Max_ge)

definition cocc_list_clear_at_pre :: \<open>occurences_ref \<Rightarrow> nat literal \<Rightarrow> bool\<close> where
  \<open>cocc_list_clear_at_pre = (\<lambda>(xs) L. nat_of_lit L < length xs)\<close>

definition cocc_list_clear_at :: \<open>occurences_ref \<Rightarrow> nat literal \<Rightarrow> occurences_ref nres\<close> where
  \<open>cocc_list_clear_at = (\<lambda>xs L . do {
     ASSERT (cocc_list_clear_at_pre xs L);
     RETURN (xs [nat_of_lit L := []])
  })\<close>

lemma cocc_list_clear_at_occ_list_clear_at:
  assumes
    \<open>(xs, \<A>xs) \<in> occurrence_list_ref\<close>
    \<open>(L,L')\<in>Id\<close>
  shows
    \<open>cocc_list_clear_at xs L \<le> \<Down>(occurrence_list_ref) (occ_list_clear_at \<A>xs L')\<close>
  using assms
  unfolding cocc_list_clear_at_def occ_list_clear_at_def case_prod_beta occurrence_list_ref_def
  apply refine_vcg
  subgoal
    by (cases L)
     (auto simp: cocc_list_clear_at_pre_def occ_list_clear_at_pre_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset
      map_fun_rel_def  dest: bspec[of _ _ L])
  subgoal
    by (cases L)
     (auto simp: cocc_list_append_pre_def occ_list_append_pre_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset
        map_fun_rel_def cocc_list_append_def occ_list_append_def; force)+
  done

definition cocc_list_clear_all_pre :: \<open>occurences_ref \<Rightarrow> bool\<close> where
  \<open>cocc_list_clear_all_pre = (\<lambda>xs. True)\<close>

definition cocc_list_clear_all :: \<open>occurences_ref \<Rightarrow> occurences_ref nres\<close> where
  \<open>cocc_list_clear_all = (\<lambda>(xs) . do {
     ASSERT (cocc_list_clear_all_pre (xs));
     RETURN (replicate (length xs) [])
  })\<close>


lemma cocc_list_clear_all_occ_list_clear_all:
  assumes
    \<open>(xs, \<A>xs) \<in> occurrence_list_ref\<close>
  shows
    \<open>cocc_list_clear_all xs \<le> \<Down>(occurrence_list_ref) (occ_list_clear_all \<A>xs)\<close>
  using assms
  unfolding cocc_list_clear_all_def occ_list_clear_all_def case_prod_beta occurrence_list_ref_def
  apply refine_vcg
  subgoal
    by
     (auto simp: cocc_list_clear_all_pre_def occ_list_clear_all_pre_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset
      map_fun_rel_def  dest: bspec[of _ _ L])
  subgoal
    by (auto simp: cocc_list_append_pre_def occ_list_append_pre_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset
        map_fun_rel_def cocc_list_append_def occ_list_append_def; force)+
  done


section \<open>Clause Marking\<close>
text \<open>
Experiment:
This should eventually replace the stuff used for the conflicts. Experiment in the current state
  to see if useful.
If it is this should be generalized. However, not clear because distinct, so not really multisets.

Experiment:
  is keeping the set of variables as sets useful?
  is the refinement from there on okay (both from doing it and also performance wise)
\<close>

subsection \<open>Abstract Representation\<close>

type_synonym clause_hash = \<open>(nat set \<times> nat clause)\<close>
definition clause_hash_ref where
  \<open>clause_hash_ref \<A> = {((\<B>, C), D). C = D \<and> set_mset \<A> = \<B> \<and> atms_of C \<subseteq> \<B>}\<close>

definition ch_create_pre :: \<open>nat set \<Rightarrow> bool\<close> where
  \<open>ch_create_pre n = (True)\<close>

text \<open>The fact that the nat set must be passed as argument is really ugly\<close>
definition mop_ch_create :: \<open>nat set \<Rightarrow> clause_hash nres\<close> where
  \<open>mop_ch_create n = do {
    ASSERT (ch_create_pre n);
    RETURN (n, {#})
  }\<close>


definition ch_add :: \<open>nat literal \<Rightarrow> clause_hash \<Rightarrow> clause_hash\<close> where
  \<open>ch_add L  =  (\<lambda>(\<A>, C). (\<A>, add_mset L C))\<close>

definition ch_add_pre :: \<open>nat literal \<Rightarrow> clause_hash \<Rightarrow> bool\<close> where
  \<open>ch_add_pre L  = (\<lambda>(\<A>, C).  atm_of L \<in> \<A> \<and> L \<notin># C)\<close>

definition mop_ch_add :: \<open>nat literal \<Rightarrow> clause_hash \<Rightarrow> clause_hash nres\<close> where
  \<open>mop_ch_add L C = do {
    ASSERT (ch_add_pre L C);
    RETURN (ch_add L C)
  }\<close>

definition ch_remove :: \<open>nat literal \<Rightarrow> clause_hash \<Rightarrow> clause_hash\<close> where
  \<open>ch_remove L = (\<lambda>(\<A>, C). (\<A>, remove1_mset L C))\<close>

definition ch_remove_pre :: \<open>nat literal \<Rightarrow> clause_hash \<Rightarrow> bool\<close> where
  \<open>ch_remove_pre L  = (\<lambda>(\<A>, C). atm_of L \<in> \<A> \<and>  L \<in>#  C)\<close>

definition mop_ch_remove :: \<open>nat literal \<Rightarrow> clause_hash \<Rightarrow> clause_hash nres\<close> where
  \<open>mop_ch_remove L C = do {
    ASSERT (ch_remove_pre L C);
    RETURN (ch_remove L C)
  }\<close>

definition ch_in :: \<open>nat literal \<Rightarrow> clause_hash \<Rightarrow> bool\<close> where
  \<open>ch_in L = (\<lambda>(\<A>, C). L \<in># C)\<close>

definition ch_in_pre :: \<open>nat literal \<Rightarrow> clause_hash \<Rightarrow> bool\<close> where
  \<open>ch_in_pre L = (\<lambda>(\<A>, C). atm_of L \<in> \<A>)\<close>

definition mop_ch_in :: \<open>nat literal \<Rightarrow> clause_hash \<Rightarrow> bool nres\<close> where
  \<open>mop_ch_in L C = do {
    ASSERT (ch_in_pre L C);
    RETURN (ch_in L C)
  }\<close>



definition ch_remove_clause :: \<open>nat clause \<Rightarrow> clause_hash \<Rightarrow> clause_hash\<close> where
  \<open>ch_remove_clause D  =  (\<lambda>(\<A>, C). (\<A>, C - D))\<close>

definition ch_remove_clause_pre :: \<open>nat clause \<Rightarrow> clause_hash \<Rightarrow> bool\<close> where
  \<open>ch_remove_clause_pre D  = (\<lambda>(\<A>, C).  D \<subseteq># C)\<close>

definition mop_ch_remove_clause :: \<open>nat clause \<Rightarrow> clause_hash \<Rightarrow> clause_hash nres\<close> where
  \<open>mop_ch_remove_clause L C = do {
    ASSERT (ch_remove_clause_pre L C);
    RETURN (ch_remove_clause L C)
  }\<close>


definition ch_remove_all :: \<open>clause_hash \<Rightarrow> clause_hash\<close> where
  \<open>ch_remove_all  =  (\<lambda>(\<A>, C). (\<A>, {#}))\<close>

definition mop_ch_remove_all :: \<open>nat clause \<Rightarrow> clause_hash \<Rightarrow> clause_hash nres\<close> where
  \<open>mop_ch_remove_all D C = do {
    ASSERT (D = snd C \<and>  atm_of ` (set_mset D) \<subseteq> fst C);
    RETURN (ch_remove_all C)
  }\<close>

definition ch_add_all :: \<open>nat clause \<Rightarrow> clause_hash \<Rightarrow> clause_hash\<close> where
  \<open>ch_add_all D =  (\<lambda>(\<A>, C). (\<A>, C + D))\<close>

definition ch_add_all_pre :: \<open>nat clause \<Rightarrow> clause_hash \<Rightarrow> bool\<close> where
  \<open>ch_add_all_pre D  = (\<lambda>(\<A>, C).  atms_of D \<subseteq> \<A> \<and> C \<inter># D = {#} \<and> distinct_mset D)\<close>

definition mop_ch_add_all :: \<open>nat clause \<Rightarrow> clause_hash \<Rightarrow> clause_hash nres\<close> where
  \<open>mop_ch_add_all L C = do {
    ASSERT (ch_add_all_pre L C);
    RETURN (ch_add_all L C)
  }\<close>

lemma mop_ch_create:
  shows \<open>mop_ch_create (set_mset \<A>) \<le> SPEC (\<lambda>c. (c, {#}) \<in> clause_hash_ref \<A>)\<close> (is \<open>?A \<le> ?B\<close>)
  unfolding mop_ch_create_def
  by refine_vcg
    (auto simp: clause_hash_ref_def ch_create_pre_def RETURN_RES_refine_iff)

lemma mop_ch_add:
  assumes \<open>(C, D) \<in> clause_hash_ref \<A>\<close> and \<open>atm_of L \<in># \<A>\<close> and \<open>(L,L')\<in>Id\<close> \<open>L\<notin>#D\<close>
  shows \<open>mop_ch_add L C \<le> SPEC(\<lambda>c. (c, add_mset L' D) \<in> clause_hash_ref \<A>)\<close>
  using assms unfolding mop_ch_add_def
  apply refine_vcg
  subgoal unfolding ch_add_pre_def by (auto simp: clause_hash_ref_def)
  subgoal by (auto simp: clause_hash_ref_def ch_add_def)
  done

lemma mop_ch_add_all:
  assumes \<open>(C, D) \<in> clause_hash_ref \<A>\<close> and \<open>atms_of L \<subseteq> set_mset \<A>\<close> and \<open>(L,L')\<in>Id\<close> \<open>D \<inter># L' = {#}\<close> and
    \<open>distinct_mset L'\<close>
  shows \<open>mop_ch_add_all L C \<le> SPEC(\<lambda>c. (c, L' + D) \<in> clause_hash_ref \<A>)\<close>
  using assms unfolding mop_ch_add_all_def
  apply refine_vcg
  subgoal unfolding ch_add_all_pre_def by (auto simp: clause_hash_ref_def)
  subgoal by (auto simp: clause_hash_ref_def ch_add_all_def)
  done

lemma mop_ch_in:
  assumes \<open>(C, D) \<in> clause_hash_ref \<A>\<close> and \<open>atm_of L \<in># \<A>\<close> and \<open>(L,L')\<in>Id\<close>
  shows \<open>mop_ch_in L C \<le> SPEC(\<lambda>c. (c, L' \<in># D) \<in> bool_rel)\<close>
  using assms unfolding mop_ch_in_def
  apply refine_vcg
  subgoal unfolding ch_in_pre_def by (auto simp: clause_hash_ref_def)
  subgoal by (auto simp: clause_hash_ref_def ch_in_def)
  done

lemma mop_ch_remove:
  assumes \<open>(C, D) \<in> clause_hash_ref \<A>\<close> and \<open>atm_of L \<in># \<A>\<close> and \<open>(L,L')\<in>Id\<close> \<open>L\<in>#D\<close>
  shows \<open>mop_ch_remove L C \<le> SPEC(\<lambda>c. (c, remove1_mset L' D) \<in> clause_hash_ref \<A>)\<close>
  using assms unfolding mop_ch_remove_def
  apply refine_vcg
  subgoal unfolding ch_remove_pre_def by (auto simp: clause_hash_ref_def)
  subgoal by (auto simp: clause_hash_ref_def ch_remove_def dest: in_atms_of_minusD)
  done

lemma mop_ch_remove_all:
  assumes \<open>(C, D) \<in> clause_hash_ref \<A>\<close> \<open>atm_of ` set_mset D \<subseteq> set_mset \<A>\<close>
  shows \<open>mop_ch_remove_all D C \<le> SPEC(\<lambda>c. (c, {#}) \<in> clause_hash_ref \<A>)\<close>
  using assms unfolding mop_ch_remove_all_def
  apply refine_vcg
  subgoal by (auto simp: clause_hash_ref_def ch_remove_all_def)
  subgoal by (auto simp: clause_hash_ref_def ch_remove_all_def)
  subgoal by (auto simp: clause_hash_ref_def ch_remove_all_def)
  done

subsection \<open>Concrete Representation\<close>

text \<open>
TODO: The mark structure should probably be replaced by our abstract ch-stuff

TODO: the alternative version consists in keeping the multiset, but replacing the atoms by the upper bound. 
This makes it possible to keep the abstraction (kind of). However, it is very clear what would be the difference.
\<close>

definition clause_hash :: \<open>(bool list \<times> clause_hash) set\<close> where
\<open>clause_hash = {(xs, (\<A>, C)). (\<forall>L \<in> snd ` D\<^sub>1 \<A>. xs ! nat_of_lit L \<longleftrightarrow> L \<in># C) \<and>
   (\<forall>L\<in>fst ` D\<^sub>1 \<A>. L < length xs) \<and> distinct_mset C}\<close>

definition mop_cch_create :: \<open>nat \<Rightarrow> bool list nres\<close> where
  \<open>mop_cch_create n = do {
    RETURN (replicate n False)
  }\<close>

lemma mop_cch_create_mop_cch_create:
  assumes \<open>\<forall>L\<in>fst ` D\<^sub>1 \<A>. L < n\<close>
  shows \<open>mop_cch_create n \<le> \<Down>clause_hash (mop_ch_create \<A>)\<close>
  using assms
  unfolding mop_cch_create_def mop_ch_create_def
  by refine_vcg
    (auto simp: clause_hash_def mset_as_position.intros)


definition cch_add :: \<open>nat literal \<Rightarrow> bool list \<Rightarrow> bool list\<close> where
  \<open>cch_add L  =  (\<lambda>C. C [nat_of_lit L := True])\<close>

definition cch_add_pre :: \<open>nat literal \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>cch_add_pre L  = (\<lambda>C. nat_of_lit L < length C)\<close>

definition mop_cch_add :: \<open>nat literal \<Rightarrow> bool list \<Rightarrow> bool list nres\<close> where
  \<open>mop_cch_add L C = do {
    ASSERT (cch_add_pre L C);
    RETURN (cch_add L C)
  }\<close>

lemma mop_cch_add_mop_cch_add:
  assumes \<open>(C, D) \<in> clause_hash\<close> and
    \<open>(L,L')\<in>Id\<close>
  shows \<open>mop_cch_add L C \<le> \<Down> clause_hash (mop_ch_add L' D)\<close>
proof -
  have [iff]: \<open>2 * x1 = Suc (2 * xa) \<longleftrightarrow> False\<close> \<open>Suc (2 * x1) = 2 * xa  \<longleftrightarrow> False\<close> for xa x1 :: nat
    by presburger+
  show ?thesis
    using assms unfolding mop_cch_add_def mop_ch_add_def clause_hash_def
    apply refine_rcg
    subgoal by (cases L) (auto simp: ch_add_pre_def cch_add_pre_def dest: bspec)
    subgoal
      by (cases L')
       (auto simp: cch_add_def ch_add_def cch_add_pre_def ch_add_pre_def intro!: mset_as_position.intros
        dest: bspec[of _ _ L'])
    done
qed


definition cch_remove :: \<open>nat literal \<Rightarrow>  bool list \<Rightarrow>  bool list\<close> where
  \<open>cch_remove L = (\<lambda>C. C[nat_of_lit L := False])\<close>

definition cch_remove_pre :: \<open>nat literal \<Rightarrow>  bool list \<Rightarrow> bool\<close> where
  \<open>cch_remove_pre L  = (\<lambda>C. nat_of_lit L < length C)\<close>

definition mop_cch_remove :: \<open>nat literal \<Rightarrow>  bool list \<Rightarrow>  bool list nres\<close> where
  \<open>mop_cch_remove L C = do {
    ASSERT (cch_remove_pre L C);
    RETURN (cch_remove L C)
  }\<close>

lemma mop_cch_remove_mop_ch_remove:
  assumes \<open>(C, D) \<in> clause_hash\<close> and
    \<open>(L,L')\<in>Id\<close>
  shows \<open>mop_cch_remove L C \<le> \<Down> clause_hash (mop_ch_remove L' D)\<close>
proof -
  have [iff]: \<open>2 * x1 = Suc (2 * xa) \<longleftrightarrow> False\<close> \<open>Suc (2 * x1) = 2 * xa  \<longleftrightarrow> False\<close> for xa x1 :: nat
    by presburger+
  show ?thesis
    using assms unfolding mop_cch_remove_def mop_ch_remove_def clause_hash_def
    apply refine_rcg
    subgoal by (cases L) (auto simp: ch_remove_pre_def cch_remove_pre_def dest: bspec)
    subgoal
      by (cases L')
        (auto simp: cch_remove_def ch_remove_def cch_remove_pre_def ch_remove_pre_def distinct_mset_remove1_All
        intro!: mset_as_position.intros
        dest: bspec[of _ _ L'])
    done
qed

definition cch_in :: \<open>nat literal \<Rightarrow>  bool list \<Rightarrow> bool\<close> where
  \<open>cch_in L = (\<lambda>C. C ! nat_of_lit L)\<close>

definition cch_in_pre :: \<open>nat literal \<Rightarrow>  bool list \<Rightarrow> bool\<close> where
  \<open>cch_in_pre L = (\<lambda>C. nat_of_lit L < length C)\<close>

definition mop_cch_in :: \<open>nat literal \<Rightarrow>  bool list \<Rightarrow> bool nres\<close> where
  \<open>mop_cch_in L C = do {
    ASSERT (cch_in_pre L C);
    RETURN (cch_in L C)
  }\<close>

lemma mop_cch_in_mop_ch_in:
  assumes \<open>(C, D) \<in> clause_hash\<close> and
    \<open>(L,L')\<in>Id\<close>
  shows \<open>mop_cch_in L C \<le> \<Down> bool_rel (mop_ch_in L' D)\<close>
proof -
  have [iff]: \<open>2 * x1 = Suc (2 * xa) \<longleftrightarrow> False\<close> \<open>Suc (2 * x1) = 2 * xa  \<longleftrightarrow> False\<close> for xa x1 :: nat
    by presburger+
  show ?thesis
    using assms unfolding mop_cch_in_def mop_ch_in_def clause_hash_def
    apply refine_rcg
    subgoal by (cases L) (auto simp: ch_in_pre_def cch_in_pre_def dest: bspec)
    subgoal
      by (cases L')
        (auto simp: cch_in_def ch_in_def cch_in_pre_def ch_in_pre_def
        intro!: mset_as_position.intros
        dest: bspec[of _ _ L'])
    done
qed


definition mop_cch_remove_all :: \<open>nat clause_l \<Rightarrow> bool list \<Rightarrow> bool list nres\<close> where
  \<open>mop_cch_remove_all C D = do {
     (_, D) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, D). i < length C)
       (\<lambda>(i, D). RETURN (i+1, D[nat_of_lit (C!i) := False]))
      (0, D);
    RETURN D
  }\<close>


abbreviation cocc_content :: \<open>nat list list \<Rightarrow> nat multiset\<close>  where
  \<open>cocc_content coccs \<equiv> sum_list (map mset coccs)\<close>

definition cocc_content_set :: \<open>nat list list \<Rightarrow> nat set\<close> where
  \<open>cocc_content_set coccs \<equiv> \<Union>(image set (set coccs))\<close>

(*TODO why doesn't that come from subset_mset.sum_list_update?*)
lemma sum_list_update_mset:
  "k < size xs \<Longrightarrow> sum_list (xs[k := x]) = sum_list xs + x - xs ! k" for xs :: \<open>'a multiset list\<close>
  unfolding sum_mset_sum_list[symmetric]
  apply (subst mset_update, assumption)
  apply (auto simp: cancel_comm_monoid_add_class.sum_mset_diff ac_simps)
  done

lemma sum_list_cocc_list_append[simp]: \<open>nat_of_lit La < length coccs \<Longrightarrow> sum_list (map mset (cocc_list_append C coccs La)) = add_mset C (sum_list (map mset coccs))\<close>
  apply (auto simp: cocc_list_append_def map_update sum_list_update sum_list_update_mset)
  done

lemma cocc_content_set_append[simp]:
  \<open>nat_of_lit La < length coccs \<Longrightarrow> cocc_content_set (cocc_list_append C coccs La) = insert C (cocc_content_set coccs)\<close>
  apply (simp only: cocc_content_set_def cocc_list_append_def in_set_upd_eq)
  apply auto
  apply (smt (verit, ccfv_threshold) in_set_conv_nth in_set_upd_cases length_Suc_rev_conv nat_neq_iff not_less_eq nth_append_first nth_append_length nth_mem)
  unfolding Bex_def
  apply (subst in_set_upd_eq, simp)
  apply (metis in_set_conv_nth length_Suc_rev_conv nat_in_between_eq(1) nth_append_length)
  by (smt (verit, best) in_set_conv_nth le_imp_less_Suc length_Suc_rev_conv length_list_update less_imp_le_nat list_update_append1 list_update_id nth_list_update_neq set_update_memI)

end