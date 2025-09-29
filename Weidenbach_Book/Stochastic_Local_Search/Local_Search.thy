(*
Title: Abstract Local Search

Author: Mara Besemer as part of the Isabelle lecture in Freiburg, SS25
Maintainer: Mathias Fleury, University of Freiburg
*)

theory Local_Search
  imports Entailment_Definition.Partial_Herbrand_Interpretation Entailment_Definition.Partial_Annotated_Herbrand_Interpretation
begin

text \<open>
There is a technique related to SAT solving called \<^emph>\<open>local search\<close>. It involves improving a random initial assignment by flipping variables to reduce the number of unsatisfied clauses. The process starts with a random assignment and evaluates the number of unsatisfied clauses. A variable is selected (often based on its impact on unsatisfied clauses) and flipped to attempt to improve the solution. This continues until either all clauses are satisfied (a solution is found) or a stopping condition (like a maximum number of iterations) is met.
Local search (or SLS) is not a decision procedure (in the sense that it cannot decide if the problem is unsatisfiable)
We do not care about termination and simply want to find a model. This week we will define the calculus and next week refine it to code.
\<close>



section \<open>Local Search (v1)\<close>

text \<open>We start with a very simple state: the assignment and the clauses.\<close>

type_synonym 'a sls_state = \<open>'a literal set \<times> 'a clauses\<close>

text \<open>
Now we define flipping: if (and only if) there is clause that is not satisfied, then you should pick any literal and flip it. The clauses do not change.
\<close>
inductive local_search :: \<open>'a sls_state \<Rightarrow> 'a sls_state \<Rightarrow> bool\<close>where

  flip: \<open>local_search (M, N) (M - {L} \<union> {-L}, N)\<close> if \<open>C \<in># N\<close> \<open>\<not>M \<Turnstile> C\<close> and \<open>L \<in> M\<close>


inductive_cases local_searchE: \<open>local_search S T\<close>

text \<open>Now we define the invariants on the transition system.\<close>
definition sls_invariant :: \<open>'a sls_state \<Rightarrow> bool\<close> where

  \<open>sls_invariant S = (consistent_interp (fst S) \<and> total_over_m (fst S) (set_mset (snd S)) \<and> {#} \<notin># snd S)\<close>



lemma sls_invariant_nonempty_model:
  assumes \<open>sls_invariant S\<close> and \<open>snd S \<noteq> {#}\<close>
  shows \<open>fst S \<noteq> {}\<close>
  using assms by (auto simp: total_over_m_def total_over_set_def atms_of_ms_def sls_invariant_def dest!: multi_member_split multi_nonempty_split)

lemma local_search_sls_invariant: \<open>local_search S T \<Longrightarrow> sls_invariant S \<Longrightarrow> sls_invariant T\<close>
  by (induction rule: local_search.induct)
   (auto simp: sls_invariant_def consistent_interp_insert_iff consistent_interp_def total_over_m_def total_over_set_def)

lemma rtranclp_local_search_sls_invariant: \<open>local_search\<^sup>*\<^sup>* S T \<Longrightarrow> sls_invariant S \<Longrightarrow> sls_invariant T\<close>
  by (induction rule: rtranclp_induct) (auto intro: local_search_sls_invariant)

lemma local_search_clauses_same: \<open>local_search S T \<Longrightarrow> snd S = snd T\<close>
  by (auto elim: local_searchE)

lemma rtranclp_local_search_clauses_same: \<open>local_search\<^sup>*\<^sup>* S T \<Longrightarrow> snd S = snd T\<close>
  by (induction rule: rtranclp_induct) (auto elim: local_search_clauses_same)


text \<open>Now prove the correctnes theorem:\<close>
lemma sls_final_state:
  assumes \<open>sls_invariant S\<close> and finished: \<open>\<And>T. \<not>local_search S T\<close>
  shows \<open>fst S \<Turnstile>sm (snd S)\<close>

proof (rule ccontr)
  assume \<open>\<not>?thesis\<close>
  then obtain C where \<open>C \<in># snd S\<close> and \<open>\<not>fst S \<Turnstile> C\<close>
    by (auto simp: true_clss_def)
  then show False
    using sls_invariant_nonempty_model[OF assms(1)] finished local_search.flip by fastforce
qed


text \<open>Prove that whenever the process terminates, then a model was found.\<close>
lemma sls_final_state_run:
  assumes \<open>local_search\<^sup>*\<^sup>* S T\<close> \<open>sls_invariant S\<close> and finished: \<open>\<And>U. \<not>local_search T U\<close>
  shows \<open>fst T \<Turnstile>sm (snd S)\<close>
  by (metis assms(1,2) finished rtranclp_local_search_clauses_same
    rtranclp_local_search_sls_invariant sls_final_state)



section \<open>Local Search (v2)\<close>

text \<open>Now we go a bit deeper and refine our previous calculus: we keep the set of \<^emph>\<open>broken\<close>
  clauses as part: this is the set of clauses that are not satisfied by the current assignment. Therefore, whenever flipping, we have to update the set.
\<close>

type_synonym 'a sls_state2 = \<open>'a literal set \<times> 'a clauses \<times> 'a clauses\<close>

abbreviation broken :: \<open>'a sls_state2 \<Rightarrow> 'a clauses\<close> where
  \<open>broken S \<equiv> snd (snd S)\<close>

abbreviation sls2_clss :: \<open>'a sls_state2 \<Rightarrow> 'a clauses\<close> where
  \<open>sls2_clss S \<equiv> fst (snd S)\<close>

text \<open>We define flipping again make sure that you update the multiset of broken clauses correctly.
  You can use syntax like \<^term>\<open>{#C \<in># N. M - {L} \<union> {-L} \<Turnstile> C#}\<close>
  to express the subset of \<^term>\<open>N\<close> such that \<^term>\<open>M - {L} \<union> {-L} \<Turnstile> C\<close>.

Express your definition in a way that only clauses where \<^term>\<open>L\<close> or  \<^term>\<open>-L\<close> are considered, for example with \<^term>\<open>{#C \<in># N. (L \<in># C \<and> P C)#}\<close>.
  \<close>
inductive local_search2 :: \<open>'a sls_state2 \<Rightarrow> 'a sls_state2 \<Rightarrow> bool\<close>where

  flip: \<open>local_search2 (M, N, br) (M - {L} \<union> {-L}, {#C \<in># N. (-L \<notin># C \<and> L \<notin># C)#} + {#C \<in># N. (-L \<in># C \<or> L \<in># C) \<and> M - {L} \<union> {-L} \<Turnstile> C#} + {#C \<in># br. (-L \<in># C)#}, br')\<close>
  if \<open>br \<noteq> {#}\<close> and \<open>L \<in> M\<close>
    \<open>br' = {#C \<in># br. (-L \<notin># C)#} + {#C \<in># N. (L \<in># C \<and> \<not>(M - {L} \<union> {-L} \<Turnstile> C))#}\<close>


inductive_cases local_search2E: \<open>local_search2 S T\<close>

fun convert_sls_state :: \<open>'a sls_state2 \<Rightarrow> 'a sls_state\<close> where
  \<open>convert_sls_state (M, N, br) = (M, N + br)\<close>


text \<open>The new invariants:\<close>
definition sls_invariant2 :: \<open>'a sls_state2 \<Rightarrow> bool\<close> where
  \<open>sls_invariant2 S = (sls_invariant (convert_sls_state S) \<and> (\<forall>C\<in># broken S. \<not>fst S \<Turnstile> C) \<and> (\<forall>C\<in># sls2_clss S. fst S \<Turnstile> C))\<close>


text \<open>One step by \<^term>\<open>local_search2\<close> is also a step in \<^term>\<open>local_search\<close>.\<close>
lemma local_search2_local_search:
  assumes \<open>local_search2 S T\<close> \<open>sls_invariant2 S\<close>
  shows \<open>local_search (convert_sls_state S) (convert_sls_state T)\<close>
  using assms
proof (induction rule: local_search2.induct)
  case (flip br L M br' N)
  let ?S = \<open>(M, N, br)\<close>
  let ?T = \<open>(M - {L} \<union> {- L},
     filter_mset ((\<Turnstile>) (M - {L} \<union> {- L})) N + filter_mset ((\<in>#) (- L)) br,
    br')\<close>
  have satis: \<open>\<And>C. C\<in># sls2_clss ?S \<Longrightarrow> fst ?S \<Turnstile> C\<close>
    using flip by (auto simp: sls_invariant2_def)
  have H: \<open>a \<in># N \<Longrightarrow> \<not> insert (- L) (M - {L}) \<Turnstile> a \<Longrightarrow> L \<in># a\<close> for a
    using satis[of a] by (auto simp: true_cls_def)
  have [simp]: \<open>{#C \<in># N. L \<in># C \<and> \<not> insert (- L) (M - {L}) \<Turnstile> C#} = {#C \<in># N. \<not> insert (- L) (M - {L}) \<Turnstile> C#}\<close>
    by (rule filter_mset_cong[of _ N]) (use H in auto)
   obtain C where \<open>C \<in># br\<close> \<open>C \<in># snd (convert_sls_state ?S)\<close> and \<open>\<not>fst ?S \<Turnstile> C\<close>
     using flip by (auto simp: sls_invariant2_def)
   moreover have \<open> {#C \<in># N. - L \<notin># C \<and> L \<notin># C#} +
     {#C \<in># N. (- L \<in># C \<or> L \<in># C) \<and> insert (- L) (M - {L}) \<Turnstile> C#} +
     filter_mset ((\<in>#) (- L)) br +
     (filter_mset ((\<notin>#) (- L)) br + {#C \<in># N. \<not> insert (- L) (M - {L}) \<Turnstile> C#}) =
     N + br\<close>
   proof -
     have \<open>({#C \<in># N. \<not> insert (- L) (M - {L}) \<Turnstile> C#} +
       ({#C \<in># N. L \<notin># C \<and> - L \<notin># C#} +
       {#C \<in># N. (L \<in># C \<or> - L \<in># C) \<and> insert (- L) (M - {L}) \<Turnstile> C#})) = N\<close> (is \<open>?A + (?B + ?C) = _\<close>)
       using satis apply (induction N) apply auto by (metis atm_of_notin_atms_of_iff flip.hyps(2) insert_Diff true_cls_insert_l
         true_cls_remove_hd_if_notin_vars)
     moreover have \<open>filter_mset ((\<in>#) (- L)) br + filter_mset ((\<notin>#) (- L)) br + A = br + A\<close> for A by fastforce
     ultimately show ?thesis
       by (auto simp: ac_simps)
   qed
   ultimately show ?case using local_search.flip[of C \<open>snd (convert_sls_state ?S)\<close> \<open>fst ?S\<close> L] flip by auto
 qed


lemma local_search2_sls_invariant:
  assumes \<open>local_search2 S T\<close> \<open>sls_invariant2 S\<close>
  shows \<open>sls_invariant2 T\<close>
  using assms local_search2_local_search[OF assms(1,2)]
proof (induction rule: local_search2.induct)
  case (flip br L M br' N)
  let ?T = \<open>(M - {L} \<union> {- L},{#C \<in># N. - L \<notin># C \<and> L \<notin># C#} +
     {#C \<in># N. (- L \<in># C \<or> L \<in># C) \<and> M - {L} \<union> {- L} \<Turnstile> C#} +
     filter_mset ((\<in>#) (- L)) br, br')\<close>
  have inv: \<open>sls_invariant (convert_sls_state ?T)\<close>
    using flip local_search_sls_invariant unfolding sls_invariant2_def by blast
  then show ?case 
    using flip apply (auto simp: sls_invariant2_def dest!: multi_member_split)
    apply (metis Diff_subset Un_commute insert_def singleton_conv
      true_cls_mono_set_mset_l true_cls_not_in_remove)
    by (metis atm_of_notin_atms_of_iff insert_Diff true_cls_insert_l
      true_cls_remove_hd_if_notin_vars)
qed
 

  
lemma rtranclp_local_search2_sls_invariant:
  assumes \<open>local_search2\<^sup>*\<^sup>* S T\<close> \<open>sls_invariant2 S\<close>
  shows \<open>sls_invariant2 T\<close>
  using assms
  by (induction rule: rtranclp_induct) (auto dest: local_search2_sls_invariant)

lemma rtranclp_local_search2_local_search:
  assumes \<open>local_search2\<^sup>*\<^sup>* S T\<close> \<open>sls_invariant2 S\<close>
  shows \<open>local_search\<^sup>*\<^sup>* (convert_sls_state S) (convert_sls_state T)\<close>
  using assms rtranclp_local_search2_sls_invariant[OF assms]
  by (induction rule: rtranclp_induct) (auto dest: local_search2_local_search simp: local_search2_sls_invariant rtranclp_local_search2_sls_invariant)

lemma local_search_local_search2:
  assumes \<open>local_search (convert_sls_state S) T\<close> \<open>sls_invariant2 S\<close>
  shows \<open>\<exists>U. local_search2 S U\<close>
  using assms
proof (induction \<open>convert_sls_state S\<close> T rule: local_search.induct)
  case (flip C N M L)
  obtain unb brok where S: \<open>S = (M, unb, brok)\<close> and N: \<open>N = unb + brok\<close>
    using flip by (cases S) auto
  have \<open>brok \<noteq> {#}\<close>
    using flip(1,2) flip(5) unfolding sls_invariant2_def S N
    by auto
  then show ?case
    using local_search2.intros(1)[of brok L M _ unb] flip(3) unfolding S by force
qed


text \<open>Now prove the overall correctness theorem. You should reuse the theorem of the first part for the satisfiability, not reprove it!\<close>
lemma full_local_search2_no_local_search:
  assumes \<open>sls_invariant2 S\<close> \<open>(\<forall>U. \<not>local_search2 T U)\<close> \<open>rtranclp local_search2 S T\<close>
  shows \<open>(\<forall>U. \<not>local_search (convert_sls_state T) U)\<close> and
    \<open>fst T \<Turnstile>sm (snd (convert_sls_state S))\<close>

proof -
  have \<open>sls_invariant2 T\<close>
    using assms(1,3) rtranclp_local_search2_sls_invariant by blast
  have \<open>local_search\<^sup>*\<^sup>* (convert_sls_state S) (convert_sls_state T)\<close>
    using assms(1,3) rtranclp_local_search2_local_search by blast
  moreover show \<open>(\<forall>U. \<not>local_search (convert_sls_state T) U)\<close>
  proof (rule ccontr)
    assume \<open>\<not>(\<forall>U. \<not>local_search (convert_sls_state T) U)\<close>
    then obtain U where \<open>local_search (convert_sls_state T) U\<close>
      by auto
    then obtain U' where \<open>local_search2 T U'\<close>
      using \<open>sls_invariant2 T\<close> local_search_local_search2 by blast
    then show False using assms(2) by auto
  qed
  ultimately show \<open>fst T \<Turnstile>sm (snd (convert_sls_state S))\<close>
    by (metis  \<open>sls_invariant2 T\<close> convert_sls_state.elims fst_swap
      rtranclp_local_search_clauses_same sls_final_state sls_invariant2_def
      snd_conv swap_simp)
qed

end
