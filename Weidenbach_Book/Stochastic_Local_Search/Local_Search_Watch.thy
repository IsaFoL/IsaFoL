(*
Title: Local Search with Single Watched Scheme

Author: Mara Besemer as part of the Isabelle lecture in Freiburg, SS25
Maintainer: Mathias Fleury, University of Freiburg
*)

theory Local_Search_Watch
  imports Local_Search 
begin

text\<open>This theory defines a variant of local search with watched literals\<close>

text\<open>old version: watched list as a collection (literal, multiset of clauses watched by literal) pairs
this approach requires existential quantification\<close>
text\<open>current version: watch lists as a datatype, where each clause stores its currently watched literal in a field (watched_lit)
This simplifies flipping since not all clauses need to be checked and each clause
has exactly one watched literal
\<close>

datatype 'a single_w_cls = WC (watched_lit: \<open>'a literal\<close>) (unwatched: \<open>'a clause\<close>)

text\<open>reconstructs the original clause from a watched clause by adding the watched literal back to the unwatched part (rest of clause)\<close>
fun clause_of :: \<open>'a single_w_cls \<Rightarrow> 'a clause\<close>  where
  \<open>clause_of (WC L C) = add_mset L C\<close>

type_synonym 'a single_w_clss = \<open>'a single_w_cls multiset\<close>

(*sls_state: M, N, br*)
type_synonym 'a sls_watch_state = \<open>'a literal set \<times> 'a single_w_clss \<times> 'a clauses\<close>

abbreviation broken :: \<open>'a sls_watch_state \<Rightarrow> 'a clauses\<close> where
  \<open>broken S \<equiv> (snd (snd S))\<close>

abbreviation sls2w_clss :: \<open>'a sls_watch_state \<Rightarrow> 'a single_w_clss\<close> where
  \<open>sls2w_clss S \<equiv> fst (snd S)\<close>

text\<open>function for mapping a literal L to the multiset of single_w_clss S whose watched_lit equals L\<close>
definition watched :: \<open>'a literal \<Rightarrow> 'a sls_watch_state \<Rightarrow> 'a single_w_cls multiset\<close> where
  \<open>watched L S \<equiv> {#C \<in># sls2w_clss S. L = watched_lit C#}\<close>


text\<open>
updating watch list:
\<forall> C watched by l (watched_lit = l):
  if other true literal l' exists:
     change watched literal
  else:
    add clause to broken

Because each clause has only one watched literal only the watched_lit is changed
The update is local and consumes exactly one single_w_cls -> for all watch lists use reflexive-transitive closure @{term"(update_flip_watched L)\<^sup>*\<^sup>* "} 
\<close>
inductive update_flip_watched :: \<open>'a literal \<Rightarrow> 'a sls_watch_state \<times> 'a single_w_clss \<Rightarrow>
    'a sls_watch_state \<times> 'a single_w_clss \<Rightarrow> bool\<close> where
  (*C \<in> watched L and L' \<in> C \<inter> M*)
  other_true_literal:
  \<open>L' \<in># clause_of C \<and> L' \<in> fst S \<Longrightarrow>
     update_flip_watched L (S, add_mset (C:: 'a single_w_cls) WL)
            ((fst S, sls2w_clss S - {#C#} + {#WC L' (remove1_mset L' (clause_of C))#}, broken S), WL)\<close>
| (*broken clauses*)
  broken_clause:
  \<open>(\<forall>L'. L' \<in># clause_of C \<longrightarrow> L' \<notin> fst S) \<Longrightarrow>
     update_flip_watched L (S, add_mset C WL)
       ((fst S, sls2w_clss S - {#C#}, add_mset (clause_of C) (broken S)), WL)\<close>


text\<open>
- \<forall> C \<in> br:
  if -L \<in> C: br - {#C#} and -L := {#C#} + watch -L
-Updating the watch list is done incrementally with update_flip_watched,
  so there is no need for a complete new computation of broken clauses or watch lists
  only local changes
\<close>

inductive watch_local_search :: \<open>'a sls_watch_state \<Rightarrow> 'a sls_watch_state \<Rightarrow> bool\<close> where
  flip:
  \<open>watch_local_search
      (M, N, br)
      (M', N'', br')\<close>
if
  \<open>M' = M - {L} \<union> {-L}\<close>
  \<open>br1 = br - {#C \<in># br. -L \<in># C#}\<close>
  \<open>N' = N + (\<lambda>C. WC (-L) (C - {#-L#})) `# {#C \<in># br. -L \<in># C#}\<close>
  \<open>(update_flip_watched L)\<^sup>*\<^sup>* ((M', N', br1), watched L (M', N', br1)) ((M', N'', br'), {#})\<close>
  \<open>L \<in> M\<close>
  \<open>br \<noteq> {#}\<close>


inductive_cases local_searchwE: \<open>watch_local_search S T\<close>


fun convert_sls_watch_state :: \<open>'a sls_watch_state \<Rightarrow> 'a sls_state\<close> where
  \<open>convert_sls_watch_state (M, N, br) = (M, image_mset clause_of N + br)\<close>

text\<open>
No need for a separate invariant about literals existing in watches, since the definition always has one watched literal
It is only necessary to check if the new watch is in the clause, and it is automatically clear that every clause
is watched by exactly one literal when updating the field in watches changes.
With the old version, it was always necessary to verify that each clause is watched by only one literal, and updates
were made by filtering, which was error prone. Also, the invariant had to be checked at every step to ensure that the watch list still contains a valid literal in the clause.
The current version makes it easier to define the invariant without searching for a literal and clause.

conditions:
- all C in broken S are unsatisfied by the current model fst S
- for every watched clause C in sls2w_clss S, the watched_lit C is present in the model fst S\<close>
  (*
Invariant: 
- sls_invariant holds
- \<Union># (watched L) = N - br (all c \<in> N \<rightarrow> one watched literal)
- all c \<in> br are not satis by M
- C \<notin> br -> min one literal in watch (C \<notin> br \<Rightarrow> \<exists> L \<in> C \<inter> M : C \<in> watch(L))
- watch list is consistent (before and after flipping)
*)

definition sls_watch_invariant :: \<open>'a sls_watch_state \<Rightarrow> bool\<close> where
  \<open>sls_watch_invariant S \<equiv> 
    (sls_invariant (convert_sls_watch_state S)) \<and>
    (\<forall>C \<in># broken S. \<not>(fst S \<Turnstile> C)) \<and>
    (\<forall>C \<in># sls2w_clss S. watched_lit C \<in> fst S)
 \<close>

fun convert_sls_watch_state_step :: \<open>'a sls_watch_state  \<times> 'a single_w_clss \<Rightarrow> 'a sls_state\<close> where
  \<open>convert_sls_watch_state_step ((M, N, br), WL) = (M, image_mset clause_of (N) + br)\<close>

text\<open>local invariant while processing the watch list\<close>
fun invariant_flipping:: \<open> 'a literal \<Rightarrow> 'a sls_watch_state \<times> 'a single_w_clss \<Rightarrow> bool\<close> where
  invariant_flipping_def[simp del]:\<open>invariant_flipping L (S, WL) \<longleftrightarrow>
    (sls_invariant (convert_sls_watch_state_step (S,WL))) \<and>
    (\<forall>C \<in># sls2w_clss S - WL. watched_lit C \<in> fst S) \<and>
    (\<forall>C \<in>#  WL. watched_lit C = L) \<and>
    (\<forall>C \<in># broken S. \<not>(fst S \<Turnstile> C)) \<and> 
     WL \<subseteq># sls2w_clss S \<and> 
    -L \<in> fst S
 \<close>
  (*broken updated before*)

lemma helper: \<open> N +A  -
               {#Ca \<in># N. watched_lit C = watched_lit Ca#} =
  {#Ca \<in># N. watched_lit C \<noteq> watched_lit Ca#} + A\<close>
  by (metis mset_remove_filtered mset_subset_eq_multiset_union_diff_commute
      multiset_filter_subset)

lemma sls_watch_invariant_fststep_update_flip_watched:
  assumes \<open>sls_watch_invariant (M, N, br)\<close> 
    \<open>L \<in> M\<close>
    \<open>br \<noteq> {#}\<close>
  shows \<open>invariant_flipping L ((M - {L} \<union> {-L},
           N+ image_mset (\<lambda>C. WC (-L) (C - {#-L#})) {#C \<in>#br. -L \<in># C#}, 
         br - {#C \<in># br. -L \<in># C#}), 
      watched L (M,N,br))\<close> (is \<open>invariant_flipping L ((?M, ?N, ?br), ?W)\<close>)
  using assms apply (auto simp: helper mset_remove_filtered sls_watch_invariant_def invariant_flipping_def watched_def)
      defer
      apply (simp add: true_cls_def)
      apply fastforce
     apply (metis uminus_not_id' single_w_cls.sel(1))
    apply (metis Diff_subset Un_insert_right sup_bot.right_neutral true_cls_mono_set_mset_l
      true_cls_not_in_remove)
   apply (simp add: subset_mset.add_increasing2)
  apply (auto simp: sls_invariant_def)
     apply (metis DiffD2 consistent_interp_insert_iff insert_Diff singleton_iff uminus_of_uminus_id)
    apply (metis atm_of_uminus atms_of_s_insert insert_Diff total_over_m_alt_def)
   apply (auto simp: total_over_m_def total_over_set_def uminus_lit_swap atms_of_ms_def)
  done


lemma sls_watch_invariant_nostep_update_flip_watched:
  assumes \<open>invariant_flipping L (S, {#})\<close>
  shows \<open>sls_watch_invariant S\<close>
  using assms unfolding invariant_flipping_def sls_watch_invariant_def by (cases S) auto


lemma sls_watch_invariant_update_flip_watched:
  assumes  \<open>update_flip_watched L S S'\<close> \<open>invariant_flipping L S\<close>
  shows \<open>invariant_flipping L S'\<close> using assms
proof (induction rule: update_flip_watched.induct)
  case (other_true_literal L' C S L WL)
  have [simp]: \<open>add_mset (clause_of C) 
       (clause_of `# remove1_mset C (sls2w_clss S) + Local_Search_Watch.broken S) =
     clause_of `# sls2w_clss S + Local_Search_Watch.broken S\<close>
    by (metis (no_types, lifting) Local_Search_Watch.invariant_flipping_def add_mset_remove_trivial_iff insert_subset_eq_iff
        msed_map_invL other_true_literal.prems union_mset_add_mset_left)
  have H: \<open>Ca \<in># add_mset (WC L' (remove1_mset L' (clause_of C))) (remove1_mset C (sls2w_clss S)) - WL ==>
       Ca = WC L' (remove1_mset L' (clause_of C)) \<or>
        (Ca \<in># sls2w_clss S - add_mset C WL)\<close> for Ca
    using other_true_literal apply auto
    by (metis (no_types, opaque_lifting) add_mset_diff_bothsides cancel_ab_semigroup_add_class.diff_right_commute
        comm_monoid_add_class.add_0 diff_diff_add_mset in_remove1_mset_neq)
  then show ?case
    using other_true_literal apply (auto simp: invariant_flipping_def)
      apply (metis convert_sls_watch_state_step.simps surjective_pairing)
     apply (auto dest!: H)[]
    by (metis insert_subset_eq_iff subset_mset_imp_subset_add_mset)
next
  case (broken_clause C S L WL)
  have [simp]: \<open>Ca \<in># sls2w_clss S - WL \<longleftrightarrow> Ca\<in># sls2w_clss S - add_mset C WL \<or> Ca = C\<close> for Ca
    by (smt (verit, ccfv_threshold) Local_Search_Watch.invariant_flipping_def add_mset_add_single broken_clause.prems
        diff_diff_add_mset diff_le_mono2_mset diff_union_cancelL in_diffD in_remove1_msetI insert_DiffM
        insert_subset_eq_iff)
  have \<open>sls_invariant (fst S, add_mset (clause_of C) (clause_of `#remove1_mset C (sls2w_clss S) + Local_Search_Watch.broken S))\<close>
    using broken_clause apply (cases S)apply (auto simp: sls_invariant_def invariant_flipping_def)
      apply (metis insert_image mset_subset_eq_insertD total_over_m_insert)
     apply (metis (no_types, lifting) image_insert insert_DiffM insert_subset_eq_iff set_mset_add_mset_insert
        total_over_m_insert)
    by (metis image_eqI in_diffD)
  then show ?case using broken_clause apply (auto simp: invariant_flipping_def)
     apply (meson true_cls_def true_lit_def)
    by (meson insert_subset_eq_iff)
qed


lemma rtranclp_sls_watch_invariant_update_flip_watched:
  assumes  \<open>(update_flip_watched L)\<^sup>*\<^sup>* S S'\<close> \<open>invariant_flipping L S\<close>
  shows \<open>invariant_flipping L S'\<close> using assms
  by (induction rule: rtranclp_induct) (auto dest: sls_watch_invariant_update_flip_watched)

lemma watch_local_search_sls_watch_invariant:
  assumes \<open>watch_local_search S T\<close> and \<open>sls_watch_invariant S\<close>
  shows \<open>sls_watch_invariant T\<close>
  using assms
proof (induction rule: watch_local_search.induct)
  case (flip  M' M L br1 br N' N N'' br')
  have start: \<open>sls_watch_invariant (M, N, br)\<close> using flip by simp 
  have step1: \<open>invariant_flipping L ((M', N', br1), watched L (M, N, br))\<close> 
    using sls_watch_invariant_fststep_update_flip_watched[OF start, of L]
    by (auto simp: flip)
  have WLMM': \<open>watched L (M, N, br) = watched L (M', N', br1)\<close>
    by (auto simp: flip watched_def filter_mset_empty_conv)
  have step2: \<open>(update_flip_watched L)\<^sup>*\<^sup>* ((M', N', br1), watched L (M', N', br1))
         ((M', N'', br'), {#})\<close>
    using flip.hyps(4) by auto
  have step3: \<open>invariant_flipping L ((M', N'', br'), {#})\<close>
    using step1 rtranclp_sls_watch_invariant_update_flip_watched[OF step2] unfolding WLMM'
    by blast
  then show ?case
    using sls_watch_invariant_nostep_update_flip_watched by blast
qed


lemma clause_equiv:
  assumes \<open>(update_flip_watched L)\<^sup>*\<^sup>* S T\<close> and \<open>invariant_flipping L S\<close>
  shows \<open>clause_of `# sls2w_clss (fst S) + broken (fst S) = clause_of `# sls2w_clss (fst T) + broken (fst T)\<close>
  using assms proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case
    by (smt (verit, ccfv_threshold) Groups.add_ac(2)
        Local_Search_Watch.invariant_flipping_def
        add_mset_add_single add_mset_remove_trivial_If
        clause_of.simps fst_conv image_mset_add_mset
        insert_subset_eq_iff prod.sel(2)
        rtranclp_sls_watch_invariant_update_flip_watched
        union_mset_add_mset_right update_flip_watched.simps) 
qed


lemma watch_local_search_local_search:
  assumes \<open>watch_local_search S T\<close> and \<open>sls_watch_invariant S\<close>
  shows \<open>local_search (convert_sls_watch_state S) (convert_sls_watch_state T)\<close>
  using assms proof (induction rule: watch_local_search.induct)
  case (flip M' M L br1 br N' N N'' br')
  have \<open> {#add_mset (- L) (remove1_mset (- L) x). x \<in># filter_mset ((\<in>#) (- L)) br#} = filter_mset ((\<in>#) (- L)) br\<close>
    by (metis (lifting) filter_mset_eq_add_msetD' insert_DiffM multiset.map_ident_strong)
  then have new_N: \<open>clause_of `# N + br = clause_of `# N' + br1\<close> using flip by auto

  have \<open>invariant_flipping L ((M', N', br1), watched L (M', N', br1))\<close>
  proof -
    have \<open>watched L (M', N', br1) = watched L (M, N, br)\<close> 
      by (auto simp: flip watched_def filter_mset_empty_conv)
    have sls_inv: \<open>sls_watch_invariant (M, N, br)\<close>
      by (simp add: flip.prems)
    have L_in_M: \<open>L \<in> M\<close> using flip by simp
    have br_not_empty: \<open>br \<noteq> {#}\<close> using flip by simp
    show ?thesis
      using sls_watch_invariant_fststep_update_flip_watched[OF sls_inv L_in_M br_not_empty] flip
      using \<open>watched L (M', N', br1) = watched L (M, N, br)\<close> by presburger
  qed
  then have \<open>clause_of `# N' + br1 = clause_of `# N'' + br'\<close>
    using clause_equiv[of L \<open>((M', N', br1), watched L (M', N', br1))\<close> \<open>((M', N'', br'), {#})\<close>]
    using flip(4) by auto
  moreover have \<open>clause_of `# N + br = clause_of `# N' + br1\<close>
    using flip
    using new_N by blast 
  obtain C where  \<open>C \<in># clause_of `# N + br\<close> \<open>\<not>M \<Turnstile> C\<close>
    using cancel_comm_monoid_add_class.diff_cancel diff_union_cancelL flip.hyps(6) flip.prems fst_conv sls_watch_invariant_def by fastforce
  then show ?case
    by (metis calculation convert_sls_watch_state.simps flip.hyps(1,5) local_search.intros new_N)
qed


lemma rtranclp_watch_local_search_local_search:
  assumes \<open>watch_local_search\<^sup>*\<^sup>* S T\<close> and \<open>sls_watch_invariant S\<close>
  shows \<open>local_search\<^sup>*\<^sup>* (convert_sls_watch_state S) (convert_sls_watch_state T)\<close>
  using assms apply (induction rule: rtranclp_induct) apply simp
  by (smt (verit, best) watch_local_search_local_search watch_local_search_sls_watch_invariant
      rtranclp.simps rtranclp_induct)

lemma watch_local_search_cannot_be_stuck:
  assumes \<open>broken S \<noteq> {#}\<close> and \<open>sls_watch_invariant S\<close>
  shows \<open>\<exists>T. watch_local_search S T\<close>
proof -            
  obtain L where \<open>L \<in> fst S\<close>
    using assms apply (cases S; cases \<open>broken S\<close>; auto simp: sls_watch_invariant_def sls_invariant_def)
    by (meson atm_of_notin_atms_of_iff multiset_nonemptyE total_over_set_def)
  define M' br1 N' where def:
    \<open>M' = fst S - {L} \<union> {-L}\<close>
    \<open>br1 = broken S - {#C \<in># broken S. -L \<in># C#}\<close>
    \<open>N' = sls2w_clss S + image_mset (\<lambda>C. WC (-L) (C - {#-L#})) {#C \<in># broken S. -L \<in># C#}\<close>
  have \<open>\<exists>N'' br'. (update_flip_watched L)\<^sup>*\<^sup>* ((M', N', br1), WL) ((M', N'', br'), {#})\<close> for WL
  proof (induction WL arbitrary: M' N' br1)
    case empty
    then show ?case by auto
  next
    case (add x WL)
    then show ?case
    proof -
      have "\<exists>m p ma. update_flip_watched L ((M', N', br1), add_mset x WL) p \<and> (update_flip_watched L)\<^sup>*\<^sup>* p ((M', ma, m), {#})"
        by (metis add broken_clause fstI other_true_literal)
      then show ?thesis
        by (meson converse_rtranclp_into_rtranclp)
    qed
  qed
  then show ?thesis using watch_local_search.flip[of M' \<open>fst S\<close> L br1 \<open>broken S\<close>
        N' \<open>sls2w_clss S\<close>] unfolding def[symmetric]
    by (metis \<open>L \<in> fst S\<close> assms(1) prod.exhaust_sel)
qed

lemma nostep_watch_local_search_no_step_local_search:
  assumes \<open>\<And>T. \<not>watch_local_search S T\<close> and \<open>sls_watch_invariant S\<close>
  shows \<open>\<And>T. \<not>local_search (convert_sls_watch_state S) T\<close>
proof -
  have \<open>broken S = {#}\<close> using watch_local_search_cannot_be_stuck[of S]
    using assms(1,2) by blast
  then have \<open>\<forall>C. C \<in># clause_of `# sls2w_clss S \<longrightarrow> (fst S \<Turnstile> C)\<close> using assms(2) apply (cases S) apply (auto simp: sls_watch_invariant_def)
    by (metis clause_of.simps true_cls_add_mset single_w_cls.exhaust_sel)

  show \<open>\<And>T. \<not>local_search (convert_sls_watch_state S) T\<close>
    by (smt (verit) \<open>Local_Search_Watch.broken S = {#}\<close> \<open>\<forall>C. C \<in># clause_of `# sls2w_clss S \<longrightarrow> fst S \<Turnstile> C\<close> add_cancel_right_right convert_sls_watch_state.simps fst_conv
        local_search.simps snd_conv surjective_pairing)
qed


lemma rtranclp_watch_local_search_sls_watch_invariant:
  assumes \<open>watch_local_search\<^sup>*\<^sup>* S T\<close> and \<open>sls_watch_invariant S\<close>
  shows \<open>sls_watch_invariant T\<close>
  using assms 
  by (induction rule: rtranclp_induct) (auto dest: watch_local_search_sls_watch_invariant)

lemma sls_final_state_run_watch:
  assumes \<open>watch_local_search\<^sup>*\<^sup>* S T\<close> \<open>sls_watch_invariant S\<close> and finished: \<open>\<And>U. \<not>watch_local_search T U\<close>
  shows \<open>fst (convert_sls_watch_state T) \<Turnstile>sm (snd (convert_sls_watch_state S))\<close>
    (*<*)
  using sls_final_state_run[of \<open>convert_sls_watch_state S\<close>  \<open>convert_sls_watch_state T\<close>]
    rtranclp_watch_local_search_local_search[OF assms(1,2)]
    nostep_watch_local_search_no_step_local_search[OF finished]
    rtranclp_watch_local_search_sls_watch_invariant[OF assms(1)]
    assms(2) unfolding sls_watch_invariant_def
  by simp
    (*>*)

end