(*
Title: Efficient Local Search with Watched Literals

Author: Mara Besemer as part of the Isabelle lecture in Freiburg, SS25
Maintainer: Mathias Fleury, University of Freiburg

In this file, we cache the wl_sls_watched lists instead of recalculating them.
*)

theory Local_Search_Watch_List
  imports Local_Search_Watch
begin

type_synonym 'a sls_watch_state_list = \<open>'a literal set \<times> 'a single_w_clss \<times> 'a clauses \<times> ('a literal \<Rightarrow> 'a single_w_cls multiset)\<close>



abbreviation wl_sls_broken :: \<open>'a sls_watch_state_list \<Rightarrow> 'a clauses\<close> where
  \<open>wl_sls_broken S \<equiv> fst (snd (snd S))\<close>

abbreviation wl_sls2w_clss :: \<open>'a sls_watch_state_list \<Rightarrow> 'a single_w_clss\<close> where
  \<open>wl_sls2w_clss S \<equiv> fst (snd S)\<close>

abbreviation wl_sls_watched :: \<open>'a sls_watch_state_list \<Rightarrow> ('a literal \<Rightarrow> 'a single_w_cls multiset)\<close> where
  \<open>wl_sls_watched S \<equiv> snd (snd (snd S))\<close>


fun convert_sls_watch_state_list :: \<open>'a sls_watch_state_list \<Rightarrow> 'a sls_watch_state\<close> where
  \<open>convert_sls_watch_state_list (M, N, br, wl) = (M, N, br)\<close>


definition sls_watch_invariant_list :: \<open>'a sls_watch_state_list \<Rightarrow> bool\<close> where
  \<open>sls_watch_invariant_list S \<equiv> 
    (sls_watch_invariant (convert_sls_watch_state_list S)) \<and>
  wl_sls_watched S = (\<lambda>L. watched L (convert_sls_watch_state_list S))\<close>

definition invariant_wl_flipping :: \<open>'a literal \<Rightarrow> 'a sls_watch_state_list \<Rightarrow> bool\<close> where
  \<open>invariant_wl_flipping L S \<equiv> 
    (invariant_flipping L (convert_sls_watch_state_list S, wl_sls_watched S L)) \<and>
    (wl_sls_watched S) = (\<lambda>L. watched L (convert_sls_watch_state_list S))
  \<close>


inductive update_flip_watched_list :: \<open>'a literal \<Rightarrow> 'a sls_watch_state_list  \<Rightarrow>
    'a sls_watch_state_list  \<Rightarrow> bool\<close> where
other_true_literal:
  \<open>L' \<in># clause_of C \<and> L' \<in> M \<Longrightarrow> WL L =  add_mset (C:: 'a single_w_cls) WL_remaining \<Longrightarrow>
     update_flip_watched_list L (M, N, br, WL)
            (M, N - {#C#} + {#WC L' (remove1_mset L' (clause_of C))#}, br, 
  WL(L:= WL_remaining, L' := WL L' + {#WC L' (remove1_mset L' (clause_of C))#}))\<close> |
broken_clause:
  \<open>(\<forall>L'. L' \<in># clause_of C \<longrightarrow> L' \<notin> M) \<Longrightarrow>  WL L = add_mset (C::'a single_w_cls) WL_remaining \<Longrightarrow>
     update_flip_watched_list L (M, N, br, WL)
       (M, N - {#C#}, add_mset (clause_of C) (br), WL(L:= WL_remaining))\<close>


text\<open>calculating WL1 instead of updating with update_flip_watched_list for simplicity\<close>
inductive watch_list_local_search :: \<open>'a sls_watch_state_list \<Rightarrow> 'a sls_watch_state_list \<Rightarrow> bool\<close> where
  flip:
  \<open>watch_list_local_search
      (M, N, br, WL)
      (M', N'', br', WL')\<close>
if
  \<open>M' = M - {L} \<union> {-L}\<close>
  \<open>br1 = br - {#C \<in># br. -L \<in># C#}\<close>
  \<open>N' = N + image_mset (\<lambda>C. WC (-L) (C - {#-L#})) {#C \<in># br. -L \<in># C#}\<close>
  \<open>WL1 = (\<lambda>L. watched L (M, N', br))\<close> 
  \<open>(update_flip_watched_list L)\<^sup>*\<^sup>* (M', N', br1, WL1) (M', N'', br', WL')\<close>
  \<open>L \<in> M\<close>
  \<open>br \<noteq> {#}\<close>
  \<open>WL' L = {#}\<close>


lemma watch_list_eq:
  assumes
    \<open>update_flip_watched_list L (M,N,br,WL) (M',N',br',WL')\<close> and
    \<open>invariant_wl_flipping L (M,N,br,WL)\<close>
  shows \<open>update_flip_watched L ((M, N, br), WL L) ((M', N', br'), WL' L)\<close>
  using assms proof cases
  case (other_true_literal L' C WL_remaining)
  have \<open>L \<noteq> L'\<close>
    by (metis Local_Search_Watch.invariant_flipping_def assms(2) consistent_interp_insert_iff
        convert_sls_watch_state_list.simps convert_sls_watch_state_step.simps fst_conv insert_Diff insert_iff
        invariant_wl_flipping_def local.other_true_literal(5) set_mset_add_mset_insert sls_invariant_def tautology_decomp'
        tautology_single)
  then show ?thesis
    by (simp add: local.other_true_literal(1,2,3,4,5,6) update_flip_watched.simps) 
next
  case (broken_clause C WL_remaining)
  then show ?thesis
    by (simp add: update_flip_watched.simps) 
qed


lemma update_flip_watched_list_correct:
  assumes \<open>update_flip_watched_list L S T\<close>
    and inv: \<open>invariant_wl_flipping L S\<close>
  shows \<open>invariant_wl_flipping L T\<close>
proof -
  obtain M N br WL M' N' br' WL' where
   ST[simp]: \<open>S = (M,N,br,WL)\<close> \<open>T = (M',N',br',WL')\<close>
   by (cases S; cases T) auto
  have \<open>update_flip_watched L ((M, N, br), WL L) ((M', N', br'), WL' L)\<close>
    using assms(1,2) by (simp add: watch_list_eq)
  then have \<open>invariant_flipping L ((M', N', br'), WL' L)\<close>
    by (metis ST(1) assms(2) convert_sls_watch_state_list.simps invariant_wl_flipping_def
        sls_watch_invariant_update_flip_watched snd_eqD)
  moreover have \<open>wl_sls_watched (M',N',br',WL') = (\<lambda>L. watched L (convert_sls_watch_state_list (M',N',br',WL')))\<close>
    using assms unfolding ST
  proof (induction rule: update_flip_watched_list.induct)
    case (other_true_literal L' C M WL L WL_remaining N br)
    moreover have \<open>L \<noteq> L'\<close>
      using other_true_literal unfolding invariant_wl_flipping_def invariant_flipping_def sls_invariant_def by (auto simp: consistent_interp_def)
    then show ?case
      using other_true_literal
      by (auto intro!: ext simp: watched_def invariant_wl_flipping_def 
          Local_Search_Watch.invariant_flipping_def)
  next
    case (broken_clause C M WL L WL_remaining N br)
    then show ?case 
      by (auto intro!: ext simp: watched_def invariant_wl_flipping_def Local_Search_Watch.invariant_flipping_def)
  qed
  ultimately show ?thesis
    unfolding invariant_wl_flipping_def by auto
qed


lemma rtranclp_sls_watch_invariant_update_flip_watched_list:
  assumes  \<open>(update_flip_watched_list L)\<^sup>*\<^sup>* S S'\<close> \<open>invariant_wl_flipping L S\<close>
  shows \<open>invariant_wl_flipping L S'\<close> using assms 
  by (induction rule: rtranclp_induct) (auto dest: update_flip_watched_list_correct)


thm watch_local_search_sls_watch_invariant

lemma sls_watch_invariant_list_nostep_update_flip_watched:
  assumes \<open>invariant_wl_flipping L S\<close> and \<open>wl_sls_watched S L = {#}\<close>
  shows \<open>sls_watch_invariant_list S\<close>
  using assms sls_watch_invariant_nostep_update_flip_watched[of L \<open>convert_sls_watch_state_list S\<close>]
  unfolding sls_watch_invariant_list_def sls_watch_invariant_def
    invariant_wl_flipping_def
  by (cases S) auto

lemma watch_list_local_search_sls_watch_invariant_list:
  assumes \<open>watch_list_local_search S T\<close> and \<open>sls_watch_invariant_list S\<close>
  shows \<open>sls_watch_invariant_list T\<close>
  using assms
proof (induction rule: watch_list_local_search.induct)
  case (flip M' M L br1 br N' N WL1 N'' br' WL' WL)
  have start: \<open>sls_watch_invariant_list (M, N, br, WL)\<close>
    \<open>sls_watch_invariant (M, N, br)\<close>
    using flip unfolding sls_watch_invariant_list_def by simp_all 
  then have step1: \<open>invariant_wl_flipping L (M', N', br1, WL1)\<close>
    unfolding invariant_wl_flipping_def sls_watch_invariant_list_def
    using sls_watch_invariant_fststep_update_flip_watched[OF start(2), of L] flip
    apply (auto simp: watched_def filter_mset_empty_conv intro!: ext)
    by (smt (verit) Diff_iff Un_iff add.right_neutral consistent_interp_def
        consistent_interp_single filter_mset_empty_conv filter_mset_eq_conv flip.hyps(1) fst_conv
        insertCI invariant_flipping.simps mset_subset_eq_multiset_union_diff_commute snd_conv
        union_iff)
  then have step3: \<open>invariant_wl_flipping L (M', N'', br', WL')\<close>
    using flip.hyps(5) rtranclp_sls_watch_invariant_update_flip_watched_list
    by blast 
  then show ?case
    using flip.hyps(8) sls_watch_invariant_list_nostep_update_flip_watched by force
qed

end
