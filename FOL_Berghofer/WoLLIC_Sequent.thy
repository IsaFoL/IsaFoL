(*
    Author: Andreas Halkjær From, DTU Compute, 2019
    Contributors: Alexander Birch Jensen, Anders Schlichtkrull & Jørgen Villadsen
*)

section \<open>Sequent Calculus\<close>

theory WoLLIC_Sequent imports WoLLIC_Tableau begin

inductive SC :: \<open>('a, 'b) form list \<Rightarrow> bool\<close> ("\<turnstile> _" 0) where
  Basic: \<open>\<turnstile> Pre i l # Neg (Pre i l) # G\<close>
| BasicNegFF: \<open>\<turnstile> Neg \<bottom> # G\<close>
| BasicTT: \<open>\<turnstile> \<top> # G\<close>
| AlphaNegNeg: \<open>\<turnstile> A # G \<Longrightarrow> \<turnstile> Neg (Neg A) # G\<close>
| AlphaNegAnd: \<open>\<turnstile> Neg A # Neg B # G \<Longrightarrow> \<turnstile> Neg (Con A B) # G\<close>
| AlphaOr: \<open>\<turnstile> A # B # G \<Longrightarrow> \<turnstile> Dis A B # G\<close>
| AlphaImpl: \<open>\<turnstile> Neg A # B # G \<Longrightarrow> \<turnstile> Imp A B # G\<close>
| BetaAnd: \<open>\<turnstile> A # G \<Longrightarrow> \<turnstile> B # G \<Longrightarrow> \<turnstile> Con A B # G\<close>
| BetaNegOr: \<open>\<turnstile> Neg A # G \<Longrightarrow> \<turnstile> Neg B # G \<Longrightarrow> \<turnstile> Neg (Dis A B) # G\<close>
| BetaNegImpl: \<open>\<turnstile> A # G \<Longrightarrow> \<turnstile> Neg B # G \<Longrightarrow> \<turnstile> Neg (Imp A B) # G\<close>
| GammaExists: \<open>\<turnstile> subst A t 0 # G \<Longrightarrow> \<turnstile> Exi A # G\<close>
| GammaNegForall: \<open>\<turnstile> Neg (subst A t 0) # G \<Longrightarrow> \<turnstile> Neg (Uni A) # G\<close>
| DeltaForall: \<open>\<turnstile> subst A (Fun n []) 0 # G \<Longrightarrow> news n (A # G) \<Longrightarrow> \<turnstile> Uni A # G\<close>
| DeltaNegExists: \<open>\<turnstile> Neg (subst A (Fun n []) 0) # G \<Longrightarrow> news n (A # G) \<Longrightarrow> \<turnstile> Neg (Exi A) # G\<close>
| Order: \<open>\<turnstile> G \<Longrightarrow> set G \<subseteq> set G' \<Longrightarrow> \<turnstile> G'\<close>

lemma Shift: \<open>\<turnstile> rotate1 G \<Longrightarrow> \<turnstile> G\<close>
  by (simp add: Order)

lemma Swap: \<open>\<turnstile> B # A # G \<Longrightarrow> \<turnstile> A # B # G\<close>
  by (simp add: Order insert_commute)

lemma \<open>\<turnstile> [Neg (Pre ''A'' []) , Pre ''A'' []]\<close>
  by (rule Shift, simp) (rule Basic)

lemma \<open>\<turnstile> [Con (Pre ''A'' []) (Pre ''B'' []), Neg (Con (Pre ''B'' []) (Pre ''A'' []))]\<close>
  apply (rule BetaAnd)
   apply (rule Swap)
   apply (rule AlphaNegAnd)
   apply (rule Shift, simp, rule Swap)
   apply (rule Basic)
  apply (rule Swap)
  apply (rule AlphaNegAnd)
  apply (rule Shift, rule Shift, simp)
  apply (rule Basic)
  done

subsection \<open>Soundness\<close>

lemma sc_soundness: \<open>\<turnstile> G \<Longrightarrow> \<exists>p \<in> set G. semantics e f g p\<close>
proof (induct G arbitrary: f rule: SC.induct)
  case (DeltaForall A n G)
  then consider
    \<open>\<forall>x. semantics e (f(n := \<lambda>w. x)) g (subst A (Fun n []) 0)\<close> |
    \<open>\<exists>x. \<exists>p \<in> set (Uni A # G). semantics e (f(n := \<lambda>w. x)) g p\<close>
    by fastforce
  then show ?case
  proof cases
    case 1
    then have \<open>\<forall>x. semantics (shift e 0 x) (f(n := \<lambda>w. x)) g A\<close>
      by simp
    then have \<open>\<forall>x. semantics (shift e 0 x) f g A\<close>
      using \<open>news n (A # G)\<close> by simp
    then show ?thesis
      by simp
  next
    case 2
    then show ?thesis
      using \<open>news n (A # G)\<close> by (metis Ball_set list_all_simps(1) params.simps(8) upd_lemma)
  qed
next
  case (DeltaNegExists A n G)
  then consider
    \<open>\<forall>x. semantics e (f(n := \<lambda>w. x)) g (Neg (subst A (Fun n []) 0))\<close> |
    \<open>\<exists>x. \<exists>p \<in> set (Neg (Exi A) # G). semantics e (f(n := \<lambda>w. x)) g p\<close>
    by fastforce
  then show ?case
  proof cases
    case 1
    then have \<open>\<forall>x. semantics (shift e 0 x) (f(n := \<lambda>w. x)) g (Neg A)\<close>
      by simp
    then have \<open>\<forall>x. semantics (shift e 0 x) f g (Neg A)\<close>
      using \<open>news n (A # G)\<close> by simp
    then show ?thesis
      by simp
  next
    case 2
    then show ?thesis
      using \<open>news n (A # G)\<close> Ball_set list_all_simps(1) params.simps(7,9) upd_lemma by metis
  qed
qed auto

subsection \<open>Tableau Calculus Equivalence\<close>

fun compl :: \<open>('a, 'b) form \<Rightarrow> ('a, 'b) form\<close> where
  \<open>compl (Neg p) = p\<close>
| \<open>compl p = Neg p\<close>

lemma compl: \<open>compl p = Neg p \<or> (\<exists>q. compl p = q \<and> p = Neg q)\<close>
  by (induct p rule: compl.induct) simp_all

lemma new_compl: \<open>new n p \<Longrightarrow> new n (compl p)\<close>
  by (cases p rule: compl.cases) simp_all

lemma news_compl: \<open>news n G \<Longrightarrow> news n (map compl G)\<close>
  using new_compl by (induct G) fastforce+

theorem TC_SC: \<open>\<stileturn> G \<Longrightarrow> \<turnstile> map compl G\<close>
proof (induct G rule: TC.induct)
  case (Basic i l G)
  then show ?case
    using SC.Basic Swap by fastforce
next
  case (AlphaNegNeg A G)
  then show ?case
    using SC.AlphaNegNeg compl by (metis compl.simps(1) list.simps(9))
next
  case (AlphaAnd A B G)
  then have *: \<open>\<turnstile> compl A # compl B # map compl G\<close>
    by simp
  then have \<open>\<turnstile> Neg A # Neg B # map compl G\<close>
    using compl AlphaNegNeg Swap by metis
  then show ?case
    using AlphaNegAnd by simp
next
  case (AlphaNegImpl A B G)
  then have \<open>\<turnstile> compl A # B # map compl G\<close>
    by simp
  then have \<open>\<turnstile> Neg A # B # map compl G\<close>
    using compl AlphaNegNeg by metis
  then show ?case
    using AlphaImpl by simp
next
  case (BetaOr A G B)
  then have \<open>\<turnstile> compl A # map compl G\<close> \<open>\<turnstile> compl B # map compl G\<close>
    by simp_all
  then have \<open>\<turnstile> Neg A # map compl G\<close> \<open>\<turnstile> Neg B # map compl G\<close>
    using compl AlphaNegNeg by metis+
  then show ?case
    using BetaNegOr by simp
next
  case (BetaImpl A G B)
  then have \<open>\<turnstile> A # map compl G\<close> \<open>\<turnstile> compl B # map compl G\<close>
    by simp_all
  then have \<open>\<turnstile> A # map compl G\<close> \<open>\<turnstile> Neg B # map compl G\<close>
    by - (assumption, metis compl AlphaNegNeg)
  then have \<open>\<turnstile> Neg (Imp A B) # map compl G\<close>
    using BetaNegImpl by blast
  then have \<open>\<turnstile> compl (Imp A B) # map compl G\<close>
    using \<open>\<turnstile> A # map compl G\<close> compl by simp
  then show ?case
    by simp
next
  case (GammaForall A t G)
  then have \<open>\<turnstile> compl (subst A t 0) # map compl G\<close>
    by simp
  then have \<open>\<turnstile> Neg (subst A t 0) # map compl G\<close>
    using compl AlphaNegNeg by metis
  then show ?case
    using GammaNegForall by simp
next
  case (DeltaExists A n G)
  then have \<open>\<turnstile> compl (subst A (Fun n []) 0) # map compl G\<close>
    by simp
  then have \<open>\<turnstile> Neg (subst A (Fun n []) 0) # map compl G\<close>
    using compl AlphaNegNeg by metis
  moreover have \<open>news n (A # map compl G)\<close>
    using DeltaExists news_compl by fastforce
  ultimately show ?case
    using DeltaNegExists by simp
next
  case (DeltaNegForall A n G)
  then have \<open>\<turnstile> subst A (Fun n []) 0 # map compl G\<close>
    by simp
  moreover have \<open>news n (A # map compl G)\<close>
    using DeltaNegForall news_compl by fastforce
  ultimately show ?case
    using DeltaForall by simp
next
  case (Order G G')
  then have \<open>set (map compl G) \<subseteq> set (map compl G')\<close>
    using set_map subset_image_iff by metis
  then show ?case
    using Order SC.Order by blast
qed (use SC.intros in simp_all)

subsection \<open>Completeness\<close>

theorem sc_completeness:
  fixes p :: \<open>(nat, nat) form\<close>
  assumes \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. list_all (semantics e f g) ps \<longrightarrow> semantics e f g p\<close>
  shows \<open>\<turnstile> p # map compl ps\<close>
proof -
  have \<open>\<stileturn> Neg p # ps\<close>
    using assms tableau_completeness unfolding tableauproof_def by simp
  then show ?thesis
    using TC_SC by fastforce
qed

corollary
  fixes p :: \<open>(nat, nat) form\<close>
  assumes \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. semantics e f g p\<close>
  shows \<open>\<turnstile> [p]\<close>
  using assms sc_completeness list.map(1) by metis

subsection \<open>Acknowledgements\<close>

text \<open>

\<^item> Mordechai (Moti) Ben-Ari:
Mathematical Logic for Computer Science.
\<^url>\<open>https://www.springer.com/gp/book/9781447141280\<close>

\<close>

end
