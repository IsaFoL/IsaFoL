(*
Title: Efficient Local Search with Watched Literals

Author: Mara Besemer as part of the Isabelle lecture in Freiburg, SS25
Maintainer: Mathias Fleury, University of Freiburg

In this file, we cache the watch lists instead of recalculating them.
*)

theory Local_Search_Watch_List
  imports Local_Search_Watch
begin

type_synonym 'a sls_state_watch_list = \<open>'a literal set \<times> 'a wclauses \<times> 'a clauses \<times> ('a literal \<Rightarrow> 'a wclause multiset)\<close>



abbreviation broken :: \<open>'a sls_state_watch_list \<Rightarrow> 'a clauses\<close> where
  \<open>broken S \<equiv> fst (snd (snd S))\<close>

abbreviation sls2w_clss :: \<open>'a sls_state_watch_list \<Rightarrow> 'a wclauses\<close> where
  \<open>sls2w_clss S \<equiv> fst (snd S)\<close>

abbreviation watch :: \<open>'a sls_state_watch_list \<Rightarrow> ('a literal \<Rightarrow> 'a wclause multiset)\<close> where
  \<open>watch S \<equiv> snd (snd (snd S))\<close>


fun convert_sls_state_watch_list :: \<open>'a sls_state_watch_list \<Rightarrow> 'a sls_state_watch\<close> where
  \<open>convert_sls_state_watch_list (M, N, br, wl) = (M, N, br)\<close>


definition sls_invariant_watch_list :: \<open>'a sls_state_watch_list \<Rightarrow> bool\<close> where
  \<open>sls_invariant_watch_list S \<equiv> 
    (sls_invariant_watch (convert_sls_state_watch_list S)) \<and>
  watch S = watches (convert_sls_state_watch_list S)
  \<close>

definition invariant_wl_step :: \<open>'a sls_state_watch_list \<Rightarrow> 'a literal \<Rightarrow> bool\<close> where
  \<open>invariant_wl_step S L \<equiv> 
    (invariant_step L (convert_sls_state_watch_list S, watch S L)) \<and>
    (watch S) = watches (convert_sls_state_watch_list S)
  \<close>


inductive update_wl_list :: \<open>'a literal \<Rightarrow> 'a sls_state_watch_list  \<Rightarrow>
    'a sls_state_watch_list  \<Rightarrow> bool\<close> where
  (*C \<in> watched L and L' \<in> C \<inter> M*)
  other_true_literal:
  \<open>L' \<in># clause_of C \<and> L' \<in> M \<Longrightarrow> WL L =  add_mset (C:: 'a wclause) WL_remaining \<Longrightarrow>
     update_wl_list L (M, N, br, WL)
            (M, N - {#C#} + {#WC L' (remove1_mset L' (clause_of C))#}, br, 
  WL(L:= WL_remaining, L' := WL L' + {#WC L' (remove1_mset L' (clause_of C))#}))\<close>
| (*broken clauses*)
  broken_clause:
  \<open>(\<forall>L'. L' \<in># clause_of C \<longrightarrow> L' \<notin> M) \<Longrightarrow>  WL L = add_mset (C::'a wclause) WL_remaining \<Longrightarrow>
     update_wl_list L (M, N, br, WL)
       (M, N - {#C#}, add_mset (clause_of C) (br), WL(L:= WL_remaining))\<close>


text\<open>calculating WL1 instead of updating with update_wl_list for simplicity\<close>
inductive local_search_watch_list :: \<open>'a sls_state_watch_list \<Rightarrow> 'a sls_state_watch_list \<Rightarrow> bool\<close> where
  flip:
  \<open>local_search_watch_list
      (M, N, br, WL)
      (M', N'', br', WL')\<close>
if
  \<open>M' = M - {L} \<union> {-L}\<close>
  \<open>br1 = br - {#C \<in># br. -L \<in># C#}\<close>
  \<open>N' = N + image_mset (\<lambda>C. WC (-L) (C - {#-L#})) {#C \<in># br. -L \<in># C#}\<close>
  \<open>WL1 = watches(M, N', br)\<close> 
  \<open>(update_wl_list L)\<^sup>*\<^sup>* (M', N', br1, WL1) (M', N'', br', WL')\<close>
  \<open>L \<in> M\<close>
  \<open>br \<noteq> {#}\<close>
  \<open>WL' L = {#}\<close>


lemma watch_list_eq:
  assumes \<open>update_wl_list L (M,N,br,WL) (M',N',br',WL')\<close>
    and \<open>invariant_wl_step (M,N,br,WL) L\<close>
  shows   \<open>update_wl L ((M, N, br), WL L) ((M', N', br'), WL' L)\<close>
  using assms proof cases
  case (other_true_literal L' C WL_remaining)
  have \<open>L \<noteq> L'\<close>
    by (metis Local_Search_Watch.invariant_step_def assms(2) consistent_interp_insert_iff
        convert_sls_state_watch_list.simps convert_sls_state_watch_step.simps fst_conv insert_Diff insert_iff
        invariant_wl_step_def local.other_true_literal(5) set_mset_add_mset_insert sls_invariant_def tautology_decomp'
        tautology_single)
  then show ?thesis
    by (simp add: local.other_true_literal(1,2,3,4,5,6) update_wl.simps) 
next
  case (broken_clause C WL_remaining)
  then show ?thesis
    by (simp add: update_wl.simps) 
qed


lemma update_wl_list_correct:
  assumes \<open>update_wl_list L (M,N,br,WL) (M',N',br',WL')\<close>
    and  inv: \<open>invariant_wl_step (M,N,br,WL) L\<close>
  shows   \<open>invariant_wl_step (M',N',br',WL') L\<close>
proof -
  have \<open>update_wl L ((M, N, br), WL L) ((M', N', br'), WL' L)\<close>
    by (simp add: assms(1,2) watch_list_eq)
  then have \<open>invariant_step L ((M', N', br'), WL' L)\<close>
    by (metis assms(2) convert_sls_state_watch_list.simps invariant_wl_step_def
        sls_invariant_watch_update_wl snd_eqD)
  moreover have \<open>watch (M',N',br',WL') = watches (convert_sls_state_watch_list (M',N',br',WL'))\<close>
    using assms
  proof (induction rule: update_wl_list.induct)
    case (other_true_literal L' C M WL L WL_remaining N br)
    moreover have \<open>L \<noteq> L'\<close>
      using other_true_literal unfolding invariant_wl_step_def invariant_step_def sls_invariant_def by (auto simp: consistent_interp_def)
    then show ?case
      using other_true_literal
      by (auto intro!: ext simp: invariant_wl_step_def Local_Search_Watch.invariant_step_def)
  next
    case (broken_clause C M WL L WL_remaining N br)
    then show ?case 
      by (auto intro!: ext simp: invariant_wl_step_def Local_Search_Watch.invariant_step_def)
  qed
  ultimately show ?thesis
    unfolding invariant_wl_step_def by auto
qed


lemma rtranclp_sls_invariant_watch_update_wl_list:
  assumes  \<open>(update_wl_list L)\<^sup>*\<^sup>* S S'\<close> \<open>invariant_wl_step S L\<close>
  shows \<open>invariant_wl_step S' L\<close> using assms 
  by (induction rule: rtranclp_induct) (auto dest: update_wl_list_correct)


thm local_search_watch_sls_invariant_watch

lemma sls_invariant_watch_list_nostep_update_wl:
  assumes \<open>invariant_wl_step S L\<close> and \<open>watch S L = {#}\<close>
  shows \<open>sls_invariant_watch_list S\<close>
  using assms sls_invariant_watch_nostep_update_wl[of L \<open>convert_sls_state_watch_list S\<close>]
  unfolding sls_invariant_watch_list_def sls_invariant_watch_def
  invariant_wl_step_def
  by (cases S) auto


text\<open>No time left to finish this lemma, but would work similar to 
local_search_watch_sls_invariant_watch\<close>
lemma local_search_watch_list_sls_invariant_watch_list:
  assumes \<open>local_search_watch_list S T\<close> and \<open>sls_invariant_watch_list S\<close>
  shows \<open>sls_invariant_watch_list T\<close>
  using assms
proof (induction rule: local_search_watch_list.induct)
  case (flip M' M L br1 br N' N WL1 N'' br' WL' WL)
  have start: \<open>sls_invariant_watch_list (M, N, br, WL)\<close>
    \<open>sls_invariant_watch (M, N, br)\<close>
    using flip unfolding sls_invariant_watch_list_def by simp_all 
  then have step1: \<open>invariant_wl_step (M', N', br1, WL1) L\<close>
    unfolding invariant_wl_step_def sls_invariant_watch_list_def
    using sls_invariant_watch_fststep_update_wl[OF start(2), of L] flip
    apply (auto simp: watched_def filter_mset_empty_conv intro!: ext)
    by (smt (verit) Diff_iff Un_iff add.right_neutral consistent_interp_def
        consistent_interp_single filter_mset_empty_conv filter_mset_eq_conv flip.hyps(1) fst_conv
        insertCI invariant_step.simps mset_subset_eq_multiset_union_diff_commute snd_conv
        union_iff)
  then have step3: \<open>invariant_wl_step (M', N'', br', WL') L\<close>
    using flip.hyps(5) rtranclp_sls_invariant_watch_update_wl_list
    by blast 
  then show ?case
    using flip.hyps(8) sls_invariant_watch_list_nostep_update_wl by force
qed

end
