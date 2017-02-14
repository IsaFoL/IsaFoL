section\<open>Proof Systems\<close>
subsection\<open>Sequent Calculus\<close>

theory SC
imports Formulas "~~/src/HOL/Library/Multiset"
begin

abbreviation msins ("_, _" [56,56] 56) where "x,M == add_mset x M"  

text\<open>The way we'd like to formulate Sequent Calculus is like this:\<close>
inductive SCp :: "form multiset \<Rightarrow> form multiset \<Rightarrow> bool" ("(_ \<Rightarrow>/ _)" [53] 53) where
BotL: "\<bottom> \<in># \<Gamma> \<Longrightarrow> \<Gamma>\<Rightarrow>\<Delta>" |
Ax: "Atom k \<in># \<Gamma> \<Longrightarrow> Atom k \<in># \<Delta> \<Longrightarrow> \<Gamma>\<Rightarrow>\<Delta>" |
NotL: "\<Gamma> \<Rightarrow> F,\<Delta> \<Longrightarrow> Not F, \<Gamma> \<Rightarrow> \<Delta>" |
NotR: "F,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> Not F, \<Delta>" |
AndL: "F,G,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> And F G, \<Gamma> \<Rightarrow> \<Delta>" |
AndR: "\<lbrakk> \<Gamma> \<Rightarrow> F,\<Delta>; \<Gamma> \<Rightarrow> G,\<Delta> \<rbrakk> \<Longrightarrow> \<Gamma> \<Rightarrow> And F G, \<Delta>" |
OrL: "\<lbrakk> F,\<Gamma> \<Rightarrow> \<Delta>; G,\<Gamma> \<Rightarrow> \<Delta> \<rbrakk> \<Longrightarrow> Or F G, \<Gamma> \<Rightarrow> \<Delta>" |
OrR: "\<Gamma> \<Rightarrow> F,G,\<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> Or F G, \<Delta>" |
ImpL: "\<lbrakk> \<Gamma> \<Rightarrow> F,\<Delta>; G,\<Gamma> \<Rightarrow> \<Delta> \<rbrakk> \<Longrightarrow> Imp F G, \<Gamma> \<Rightarrow> \<Delta>" |
ImpR: "F,\<Gamma> \<Rightarrow> G,\<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> Imp F G, \<Delta>"

text\<open>However, we'd like to follow Troelstra and Schwichtenberg~\cite{troelstra2000basic} with many of our proofs.
They often use induction on the depth of the derivation.
In many cases, rule induction does suffice, but using an induction over the depth yields easier to understand proofs,
at least subjectively.
\<close>
inductive SCc :: "form multiset \<Rightarrow> form multiset \<Rightarrow> nat \<Rightarrow> bool" ("((_ \<Rightarrow>/ _) \<down> _)" [53,53] 53) where
BotL: "\<bottom> \<in># \<Gamma> \<Longrightarrow> \<Gamma>\<Rightarrow>\<Delta> \<down> Suc n" |
Ax: "Atom k \<in># \<Gamma> \<Longrightarrow> Atom k \<in># \<Delta> \<Longrightarrow> \<Gamma>\<Rightarrow>\<Delta> \<down> Suc n" |
NotL: "\<Gamma> \<Rightarrow> F,\<Delta> \<down> n \<Longrightarrow> Not F, \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n" |
NotR: "F,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> Not F, \<Delta> \<down> Suc n" |
AndL: "F,G,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> And F G, \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n" |
AndR: "\<lbrakk> \<Gamma> \<Rightarrow> F,\<Delta> \<down> n; \<Gamma> \<Rightarrow> G,\<Delta> \<down> n \<rbrakk> \<Longrightarrow> \<Gamma> \<Rightarrow> And F G, \<Delta> \<down> Suc n" |
OrL: "\<lbrakk> F,\<Gamma> \<Rightarrow> \<Delta> \<down> n; G,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<rbrakk> \<Longrightarrow> Or F G, \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n" |
OrR: "\<Gamma> \<Rightarrow> F,G,\<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> Or F G, \<Delta> \<down> Suc n" |
ImpL: "\<lbrakk> \<Gamma> \<Rightarrow> F,\<Delta> \<down> n; G,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<rbrakk> \<Longrightarrow> Imp F G, \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n" |
ImpR: "F,\<Gamma> \<Rightarrow> G,\<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> Imp F G, \<Delta> \<down> Suc n"

lemma
  shows BotL_canonical: "\<bottom>,\<Gamma>\<Rightarrow>\<Delta>"
    and Ax_canonical: "Atom k,\<Gamma> \<Rightarrow> Atom k,\<Delta>"
  by (meson SCp.intros union_single_eq_member)+
    
lemma deeper: "\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta> \<down> n + m"
  by(induction rule: SCc.induct; insert SCc.intros; auto) 
lemma deeper_suc: "\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n"
  (* this version is actually required more often. It can be declared as an elim!, but I want to make its usage explicit *)
  thm deeper[unfolded Suc_eq_plus1[symmetric]]
  by(drule deeper[where m=1]) simp
    
text\<open>The equivalence is obvious.\<close>
theorem SC_SCp_eq: "(\<exists>n. \<Gamma> \<Rightarrow> \<Delta> \<down> n) \<longleftrightarrow> \<Gamma> \<Rightarrow> \<Delta>" (is "?c \<longleftrightarrow> ?p")
proof
  assume ?c then guess n ..
  thus ?p by(induction rule: SCc.induct; simp add: SCp.intros)
next
  have deeper_max: "\<Gamma> \<Rightarrow> \<Delta> \<down> max m n" "\<Gamma> \<Rightarrow> \<Delta> \<down> max n m" if "\<Gamma> \<Rightarrow> \<Delta> \<down> n" for n m \<Gamma> \<Delta>
  proof -
    have "n \<le> m \<Longrightarrow> \<exists>k. m = n + k" by presburger
    with that[THEN deeper] that
    show "\<Gamma> \<Rightarrow> \<Delta> \<down> max n m" unfolding max_def by clarsimp
    thus "\<Gamma> \<Rightarrow> \<Delta> \<down> max m n" by (simp add: max.commute)
  qed
  assume ?p thus ?c by(induction rule: SCp.induct)
      (insert SCc.intros deeper_max; metis)+
qed

(* it makes a difference whether we say Ax is 0 or any: with Ax \<down> 0 we could not prove the deepening rules.
   Also, it is important to allow only atoms in Ax, otherwise the inv-rules are not depth preserving.
  Making Ax/BotL start from \<ge>1 saves proving the base-cases twice
 *)
lemma no_0_SC[dest!]: "\<Gamma> \<Rightarrow> \<Delta> \<down> 0 \<Longrightarrow> False"
  by(cases rule: SCc.cases[of \<Gamma> \<Delta> 0]) assumption


lemma lem1: "x \<noteq> y \<Longrightarrow> x, M = y,N \<longleftrightarrow> x \<in># N \<and> M = y,(N - {#x#})"
  by (metis (no_types, lifting) add_eq_conv_ex add_mset_remove_trivial add_mset_remove_trivial_eq)

lemma lem2: "x \<noteq> y \<Longrightarrow> x, M = y, N \<longleftrightarrow> y \<in># M \<and> N = x, (M - {#y#})"
  using lem1 by fastforce

text\<open>This is here to deal with a technical problem: the way the simplifier uses @{thm add_mset_commute} is really suboptimal for the unification of SC rules.\<close>
  
lemma sc_insertion_ordering[simp]:
  "NO_MATCH (I\<^bold>\<rightarrow>J) H \<Longrightarrow> H,F\<^bold>\<rightarrow>G,S = F\<^bold>\<rightarrow>G,H,S"
  "NO_MATCH (I\<^bold>\<rightarrow>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<or>J) H \<Longrightarrow> H,F\<^bold>\<or>G,S = F\<^bold>\<or>G,H,S"
  "NO_MATCH (I\<^bold>\<rightarrow>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<or>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<and>J) H \<Longrightarrow> H,F\<^bold>\<and>G,S = F\<^bold>\<and>G,H,S"
  "NO_MATCH (I\<^bold>\<rightarrow>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<or>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<and>J) H \<Longrightarrow> NO_MATCH (\<^bold>\<not>J) H \<Longrightarrow> H,\<^bold>\<not>G,S = \<^bold>\<not>G,H,S"
  "NO_MATCH (I\<^bold>\<rightarrow>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<or>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<and>J) H \<Longrightarrow> NO_MATCH (\<^bold>\<not>J) H \<Longrightarrow> NO_MATCH (\<bottom>) H \<Longrightarrow> H,\<bottom>,S = \<bottom>,H,S"
  "NO_MATCH (I\<^bold>\<rightarrow>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<or>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<and>J) H \<Longrightarrow> NO_MATCH (\<^bold>\<not>J) H \<Longrightarrow> NO_MATCH (\<bottom>) H \<Longrightarrow> NO_MATCH (Atom k) H \<Longrightarrow> H,Atom l,S = Atom l,H,S"
  (* I have decided that \<bottom> and atoms should be pulled outwards with the lowest priorities. this may not always be smart. *)
by simp_all

lemma inR1: "\<Gamma> \<Rightarrow> G, H, \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> H, G, \<Delta> \<down> n" by(simp add: add_mset_commute)
lemma inL1: "G, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> H, G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" by(simp add: add_mset_commute)
lemma inR2: "\<Gamma> \<Rightarrow> F, G, H, \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> G, H, F, \<Delta> \<down> n" by(simp add: add_mset_commute)
lemma inL2: "F, G, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> G, H, F, \<Gamma> \<Rightarrow> \<Delta> \<down> n" by(simp add: add_mset_commute)
lemma inR3: "\<Gamma> \<Rightarrow> F, G, H, \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> H, F, G, \<Delta> \<down> n" by(simp add: add_mset_commute)
lemma inR4: "\<Gamma> \<Rightarrow> F, G, H, I, \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> H, I, F, G, \<Delta> \<down> n" by(simp add: add_mset_commute)
lemma inL3: "F, G, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> H, F, G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" by(simp add: add_mset_commute)
lemma inL4: "F, G, H, I, \<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> H, I, F, G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" by(simp add: add_mset_commute)
lemmas SC_swap_applies[elim!] = inL1 inL2 inL3 inL4 inR1 inR2 inR3 inR4
  (* these are here because they can be used for more careful reasoning with intro *)

lemma "Atom C \<^bold>\<rightarrow> Atom D \<^bold>\<rightarrow> Atom E,
       Atom k \<^bold>\<rightarrow> Atom C \<^bold>\<and> Atom D, 
       Atom k, {#} 
\<Rightarrow> {# Atom E #} \<down> Suc (Suc (Suc (Suc (Suc 0))))"
  by(auto intro!: SCc.intros(3-) intro: SCc.intros(1,2))

lemma NotL_inv: "Not F, \<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta> \<down> n"
proof(induction "Not F, \<Gamma>" "\<Delta>" n arbitrary: F \<Gamma> rule: SCc.induct)
  case (Ax k \<Delta>)
(* important that the principal formula is required to be an atom *)
  hence "Atom k \<in># \<Gamma>" by simp
  thus ?case using Ax SCc.Ax by simp
next
  case BotL thus ?case by(simp add: SCc.BotL)
next
  case (NotL \<Gamma>' G \<Delta> n)
  show ?case
  proof cases
    assume "\<^bold>\<not>G = \<^bold>\<not>F" thus ?thesis using NotL deeper_suc by auto
  next
    assume "\<^bold>\<not>G \<noteq> \<^bold>\<not>F"
    from this[THEN lem2] show ?thesis using NotL
      by(auto simp add: lem2 SCc.NotL add_mset_commute)
  qed
next
  case NotR thus ?case using SCc.NotR by (metis add_mset_commute)
next
  case (AndL  G H \<Gamma>' \<Delta> n')
  from AndL(3) have "G, H, \<Gamma>' = \<^bold>\<not> F, G, H, (\<Gamma> - {# And G H #})" by (metis add_eq_conv_diff add_mset_remove_trivial form.distinct(19))
  from this[THEN AndL(2)]
  show ?case using AndL(3) by (metis SCc.AndL form.simps(25) insert_DiffM insert_noteq_member)
next
  case AndR thus ?case by (simp add: AndR.hyps(2) SCc.AndR inR1)
next
  case (OrL G \<Gamma>' \<Delta> n' H)
  from this(5) have a: "H, \<Gamma>' = \<^bold>\<not> F, H, (\<Gamma> - {#G \<^bold>\<or> H#})" using union_single_eq_diff by fastforce
  from OrL(5) have b: "G, \<Gamma>' = \<^bold>\<not> F, G, (\<Gamma> - {#G \<^bold>\<or> H#})" using union_single_eq_diff by fastforce
  note * = OrL(2)[OF b] OrL(4)[OF a]
  thus ?case using OrL(5) by (metis SCc.OrL form.distinct(21) insert_DiffM insert_noteq_member)
next
  case OrR thus ?case by (simp add: OrR.hyps(2) SCc.OrR inR1 inR2)
next
  case ImpL thus ?case using lem2[OF form.simps(29)] SCc.ImpL inR1 by simp
next
  case ImpR thus ?case by (metis SCc.ImpR add_mset_commute)
qed

lemma AndL_inv: "And F G, \<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> F,G,\<Gamma> \<Rightarrow> \<Delta> \<down> n"
proof(induction n arbitrary: \<Gamma> \<Delta>)
  case (Suc n)
  have And_in[simp]: "K,And F G,S = And F G,K,S" for K S by simp
  have not_principal[dest!]: "And F G, \<Gamma> = F', \<Gamma>' \<Longrightarrow> And F G \<noteq> F' \<Longrightarrow> 
    \<Gamma> = F', \<Gamma>' - {# And F G #} \<and> F \<^bold>\<and> G, \<Gamma>' - {#F \<^bold>\<and> G#} = \<Gamma>'" for F' \<Gamma>' by (simp add: lem1 insert_DiffM)
  note swaps[intro] = inL1 inL2 inL4 inR1 inR2 inR4
  note IHm[intro!] = swaps[OF Suc.IH] Suc.IH
  note SCI[intro!] = SCc.intros(3-10)
  from Suc.prems show ?case proof(cases rule: SCc.cases[of "And F G,\<Gamma>" \<Delta> "Suc n"])
    case BotL thus ?thesis by(intro SCc.BotL) simp
  next
    case (Ax k) thus ?thesis by(intro SCc.Ax[of k]; simp)
  next
    case (AndL F' G' \<Delta>') thus ?thesis 
      by(cases "And F G = And F' G'") (force intro!: swaps[OF SCc.AndL] elim!: deeper_suc)+
  qed fastforce+
qed blast


lemma OrL_inv: 
  assumes "Or F G, \<Gamma> \<Rightarrow> \<Delta> \<down> n"
  shows "F,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<and> G,\<Gamma> \<Rightarrow> \<Delta> \<down> n"
proof(insert assms, induction n arbitrary: \<Gamma> \<Delta>)
  case (Suc n)
  have Or_in[simp]: "K,Or F G,S = Or F G,K,S" for K S by simp
  have not_principal[dest!]: "Or F G, \<Gamma> = F', \<Gamma>' \<Longrightarrow> Or F G \<noteq> F' \<Longrightarrow> 
    \<Gamma> = F', \<Gamma>' - {# Or F G #} \<and> Or F G, \<Gamma>' - {#Or F G#} = \<Gamma>'" for F' \<Gamma>' by (simp add: lem1 insert_DiffM)
  note swaps[intro] = inL1 inL2 inL4 inR1 inR2 inR4
  note IHm[intro!] = swaps[OF Suc.IH[THEN conjunct1]] swaps[OF Suc.IH[THEN conjunct2]] 
                     Suc.IH[THEN conjunct1] Suc.IH[THEN conjunct2]
  note SCI[intro!] = SCc.intros(3-10)
  from Suc.prems show ?case proof(cases rule: SCc.cases[of "Or F G,\<Gamma>" \<Delta> "Suc n"])
    case BotL thus ?thesis by(intro conjI SCc.BotL) simp_all
  next
    case (Ax k) thus ?thesis by(intro conjI SCc.Ax[of k]; simp)
  next
    case (OrL F' \<Delta>' G') thus ?thesis by(cases "Or F G = Or F' G'") (force intro!: swaps[OF SCc.OrL] elim!: deeper_suc)+
  qed force+
qed blast

lemma ImpL_inv: 
  assumes "Imp F G, \<Gamma> \<Rightarrow> \<Delta> \<down> n"
  shows "\<Gamma> \<Rightarrow> F,\<Delta> \<down> n \<and> G,\<Gamma> \<Rightarrow> \<Delta> \<down> n"
proof(insert assms, induction n arbitrary: \<Gamma> \<Delta>)
  case (Suc n)
  have Imp_in[simp]: "K,Imp F G,S = Imp F G,K,S" for K S by simp
  have not_principal[dest!]: "Imp F G, \<Gamma> = F', \<Gamma>' \<Longrightarrow> Imp F G \<noteq> F' \<Longrightarrow> 
    \<Gamma> = F', \<Gamma>' - {# Imp F G #} \<and> Imp F G, \<Gamma>' - {#Imp F G#} = \<Gamma>'" for F' \<Gamma>' by (simp add: lem1 insert_DiffM)
  note swaps[intro] = inL1 inL2 inL4 inR1 inR2 inR4
  note IHm[intro!] = swaps[OF Suc.IH[THEN conjunct1]] swaps[OF Suc.IH[THEN conjunct2]] 
                     Suc.IH[THEN conjunct1] Suc.IH[THEN conjunct2]
  note SCI[intro!] = SCc.intros(3-10)
  from Suc.prems show ?case proof(cases rule: SCc.cases[of "Imp F G,\<Gamma>" \<Delta> "Suc n"])
    case BotL thus ?thesis by(intro conjI SCc.BotL) simp_all
  next
    case (Ax k) thus ?thesis by(intro conjI SCc.Ax[of k]; simp)
  next
    case (ImpL \<Delta>' F' G') thus ?thesis by(cases "Imp F G = Imp F' G'") (force elim!: deeper_suc)+
  qed force+
qed blast

lemma ImpR_inv:
  assumes "\<Gamma> \<Rightarrow> Imp F G,\<Delta> \<down> n"
  shows "F,\<Gamma> \<Rightarrow> G,\<Delta> \<down> n"
proof(insert assms, induction n arbitrary: \<Gamma> \<Delta>)
  case (Suc n)
  have not_principal[dest]: "Imp F G, \<Delta> = F', \<Delta>' \<Longrightarrow> Imp F G \<noteq> F' \<Longrightarrow> 
    \<Delta> = F', \<Delta>' - {# Imp F G #} \<and> F \<^bold>\<rightarrow> G, \<Delta>' - {#F \<^bold>\<rightarrow> G#} = \<Delta>'" for F' \<Delta>' by (simp add: lem1 insert_DiffM)
  note swaps[intro] = inR1 inR2 inL1 inL2
  note IHm[intro!] = swaps[OF Suc.IH]
  note SCI[intro!] = SCc.intros(3-10)
  note I = IHm SCI
  from Suc.prems show ?case proof(cases rule: SCc.cases[of \<Gamma> "Imp F G, \<Delta>" "Suc n"])
    case BotL thus ?thesis by(intro SCc.BotL) simp
  next
    case (Ax k) thus ?thesis by(intro SCc.Ax[of k]; simp)
  next
    case (ImpR F' G' \<Delta>') thus ?thesis by(cases "Imp F G = Imp F' G'"; force elim!: deeper_suc)
  qed force+
qed blast

lemma AndR_inv_pre:
shows "\<Gamma> \<Rightarrow> And F G, \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> F, \<Delta> \<down> n \<and> \<Gamma> \<Rightarrow> G, \<Delta> \<down> n"
proof(induction n arbitrary: \<Gamma> \<Delta>)
  case 0 thus ?case by(cases rule: SCc.cases[of \<Gamma> "And F G, \<Delta>" 0]; simp add: SCc.intros)
next
  case (Suc n)
  have not_principal[dest]: "And F G, \<Delta> = F', \<Delta>' \<Longrightarrow> And F G \<noteq> F' \<Longrightarrow> 
    \<Delta> = F', \<Delta>' - {# And F G #} \<and> F \<^bold>\<and> G, \<Delta>' - {#F \<^bold>\<and> G#} = \<Delta>'" for F' \<Delta>' by (simp add: lem1 insert_DiffM)
  note swaps[intro] = inR1 inR2 inL1 inL2
  note IHm[intro!] = swaps[OF Suc.IH[THEN conjunct1]] swaps[OF Suc.IH[THEN conjunct2]]
  note Suc.IH[dest]
  note SCI[intro!] = SCc.intros(3-10)
  note I = IHm SCI
  from Suc.prems show ?case proof(cases rule: SCc.cases[of \<Gamma> "And F G, \<Delta>" "Suc n"])
    case BotL thus ?thesis by(intro SCc.BotL conjI) simp
  next
    case (Ax k) thus ?thesis by(intro conjI SCc.Ax[of k]; simp)
  next
    case (AndR F' \<Delta>' G') thus ?thesis by(cases "And F G = And F' G'"; fastforce elim!: deeper_suc)
  next
    case NotR thus ?thesis using SCc.NotR Suc.IH form.distinct(19) not_principal by auto
  qed force+
qed
lemmas AndR_inv = AndR_inv_pre[THEN conjunct1] AndR_inv_pre[THEN conjunct2]

lemma OrR_inv: "\<Gamma> \<Rightarrow> Or F G, \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> F,G,\<Delta> \<down> n"
proof(induction n arbitrary: \<Gamma> \<Delta>)
  case (Suc n)
  have not_principal[dest]: "Or F G, \<Delta> = F', \<Delta>' \<Longrightarrow> Or F G \<noteq> F' \<Longrightarrow> 
    \<Delta> = F', \<Delta>' - {# Or F G #} \<and> Or F G, \<Delta>' - {# Or F G#} = \<Delta>'" for F' \<Delta>' by (simp add: lem1 insert_DiffM)
  note swaps[intro] = inR1 inR2 inL1 inL2 inL4 inR4
  note IHm[intro!] = swaps[OF Suc.IH]
  note SCI[intro!] = SCc.intros(3-10)
  note I = IHm SCI
  from Suc.prems show ?case proof(cases rule: SCc.cases[of \<Gamma> "Or F G, \<Delta>" "Suc n"])
    case BotL thus ?thesis by(intro SCc.BotL) simp
  next
    case (Ax k) thus ?thesis by(intro SCc.Ax[of k]; simp)
  next
    case (OrR F' G' \<Delta>') thus ?thesis using not_principal by(cases "Or F G = Or F' G'"; auto elim!: deeper_suc simp add: inR3)
  qed (insert not_principal, fastforce)+
qed blast

lemma NotR_inv: "\<Gamma> \<Rightarrow> Not F, \<Delta> \<down> n \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta> \<down> n"
proof(induction n arbitrary: \<Gamma> \<Delta>)
  case (Suc n)
  have not_principal[dest]: "Not F, \<Delta> = F', \<Delta>' \<Longrightarrow> Not F \<noteq> F' \<Longrightarrow> 
    \<Delta> = F', \<Delta>' - {# Not F #} \<and> Not F, \<Delta>' - {# Not F#} = \<Delta>'" for F' \<Delta>' by (simp add: lem1 insert_DiffM)
  note swaps[intro] = inR1 inR2 inL1 inL2
  note IHm[intro!] = swaps[OF Suc.IH] Suc.IH
  note SCI[intro!] = SCc.intros(3-10)
  note I = IHm SCI
  from Suc.prems show ?case proof(cases rule: SCc.cases[of \<Gamma> "Not F, \<Delta>" "Suc n"])
    case BotL thus ?thesis by(intro SCc.BotL) simp
  next
    case (Ax k) thus ?thesis by(intro SCc.Ax[of k]; simp)
  next
    case (NotR F' \<Delta>') thus ?thesis by(cases "Not F = Not F'"; fastforce elim!: deeper_suc)
  next
  qed (fastforce simp del: sc_insertion_ordering)+
qed blast

lemma weakenL: "\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta> \<down> n"
by(induction rule: SCc.induct) 
  (auto intro!: SCc.intros(3-) intro: SCc.intros(1,2))

lemma weakenR: "\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta> \<down> n"
by(induction rule: SCc.induct)
  (auto intro: SCc.intros(3-) simp add: SCc.intros(1,2))

lemma weakenL_set: "\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> F + \<Gamma> \<Rightarrow> \<Delta> \<down> n"
  by(induction F; simp add: weakenL) 
lemma weakenR_set: "\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> F + \<Delta> \<down> n"
  by(induction F; simp add: weakenR)

text\<open>The price we have to pay for using two different predicates is lifting all those lemmata.\<close>
lemma
  shows NotL_inv': "Not F, \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta>"
  and NotR_inv': "\<Gamma> \<Rightarrow> Not F, \<Delta> \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta>"
  and AndL_inv': "And F G, \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> F,G,\<Gamma> \<Rightarrow> \<Delta>"
  and AndR_inv': "\<Gamma> \<Rightarrow> And F G, \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> F, \<Delta> \<and> \<Gamma> \<Rightarrow> G, \<Delta>"
  and OrL_inv': "Or F G, \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta> \<and> G,\<Gamma> \<Rightarrow> \<Delta>"
  and OrR_inv': "\<Gamma> \<Rightarrow> Or F G, \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> F,G,\<Delta>"
  and ImpL_inv': "F \<^bold>\<rightarrow> G, \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> F, \<Delta> \<and> G, \<Gamma> \<Rightarrow> \<Delta>"
  and ImpR_inv': "\<Gamma> \<Rightarrow> Imp F G,\<Delta> \<Longrightarrow> F,\<Gamma> \<Rightarrow> G,\<Delta>"
  and weakenL': "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta>" 
  and weakenR': "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta>"
  and weakenL_set': "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Theta> + \<Gamma> \<Rightarrow> \<Delta>" 
  and weakenR_set': "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Theta> + \<Delta>"
  unfolding SC_SCp_eq[symmetric]
  using NotL_inv AndL_inv OrL_inv ImpL_inv ImpR_inv AndR_inv OrR_inv NotR_inv weakenL weakenR weakenL_set weakenR_set by metis+
lemma
    shows PlainBotL'[intro!]: "\<bottom>,\<Gamma> \<Rightarrow> \<Delta>" using SCp.BotL by simp
lemma shows
     inR1': "\<Gamma> \<Rightarrow> G, H, \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> H, G, \<Delta>"
 and inL1': "G, H, \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> H, G, \<Gamma> \<Rightarrow> \<Delta>"
 and inR2': "\<Gamma> \<Rightarrow> F, G, H, \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> G, H, F, \<Delta>"
 and inL2': "F, G, H, \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> G, H, F, \<Gamma> \<Rightarrow> \<Delta>" by(simp_all add: add_mset_commute)
lemmas SCp_swap_applies[elim!,intro] = inL1' inL2' inR1' inR2'

lemma extended_Ax: "\<Gamma> \<inter># \<Delta> \<noteq> {#} \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
proof -
  assume "\<Gamma> \<inter># \<Delta> \<noteq> {#}"
  then obtain W where "W \<in># \<Gamma>" "W \<in># \<Delta>" by force
  then show ?thesis proof(induction W arbitrary: \<Gamma> \<Delta>)
    case (Not W)
    from Not.prems obtain \<Gamma>' \<Delta>' where [simp]: "\<Gamma> = Not W,\<Gamma>'" "\<Delta> = Not W,\<Delta>'" by (metis insert_DiffM)
    have "W \<in># W,\<Gamma>'" "W \<in># W,\<Delta>'" by simp_all
    from Not.IH[OF this] obtain n where "W, \<Gamma>' \<Rightarrow> W, \<Delta>'" by presburger
    hence "Not W, \<Gamma>' \<Rightarrow> Not W, \<Delta>'" using SCp.intros(3,4) add_mset_commute by metis
    thus "\<Gamma> \<Rightarrow> \<Delta>" by auto
  next
    case (And G H)
    from And.prems obtain \<Gamma>' \<Delta>' where [simp]: "\<Gamma> = And G H,\<Gamma>'" "\<Delta> = And G H,\<Delta>'" by (metis insert_DiffM)
    have "G \<in># G, H, \<Gamma>'" "G \<in># G, \<Delta>'" by simp_all
    with And.IH(1) have IH1: "G, H, \<Gamma>' \<Rightarrow> G, \<Delta>'" .
    have "H \<in># G, H, \<Gamma>'" "H \<in># H, \<Delta>'" by simp_all
    with And.IH(2) have IH2: "G, H, \<Gamma>' \<Rightarrow> H, \<Delta>'" .
    from IH1 IH2 have "G, H, \<Gamma>' \<Rightarrow> G, \<Delta>'" "G, H, \<Gamma>' \<Rightarrow> H, \<Delta>'" by fast+
    thus "\<Gamma> \<Rightarrow> \<Delta>" using SCp.intros(5,6) by fastforce
  next
    case (Or G H)
    case (Imp G H)
    text\<open>analogously\<close> (*<*)
  next
    case (Or G H)
    from Or.prems obtain \<Gamma>' \<Delta>' where [simp]: "\<Gamma> = Or G H,\<Gamma>'" "\<Delta> = Or G H,\<Delta>'" by (metis insert_DiffM)
    with Or.IH show ?case using SCp.intros(7,8) by fastforce
  next
    case (Imp G H)
    from Imp.prems obtain \<Gamma>' \<Delta>' where [simp]: "\<Gamma> = Imp G H,\<Gamma>'" "\<Delta> = Imp G H,\<Delta>'" by (metis insert_DiffM)
    from Imp.IH have "G, \<Gamma>' \<Rightarrow> G, H, \<Delta>'" "H, G, \<Gamma>' \<Rightarrow> H, \<Delta>'" by simp_all
    thus ?case by(auto intro!: SCp.intros(3-))
  (*>*)
  qed (auto intro: SCp.intros)
qed
thm diff_union_swap
lemma Cut_Bot_pre: "\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>-{#\<bottom>#} \<down> n"
proof(induction rule: SCc.induct) 
  case BotL thus ?case by(rule SCc.BotL; simp) (* SC.BotL refers to SC.SCp.BotL. Even more interestingly, there used to be a SCc.SC.BotL (which was not reffered to). I'll just leave this here and see how long till someone breaks it. *)
next case (Ax k) thus ?case by(intro SCc.Ax[of k]; simp; metis diff_single_trivial form.distinct(1) insert_DiffM lem1)
next case NotL thus ?case using SCc.NotL by (metis add_mset_remove_trivial diff_single_trivial diff_union_swap insert_DiffM)
next case NotR thus ?case using SCc.NotR by (metis diff_union_swap form.distinct(11))
next case AndR thus ?case using SCc.AndR by (metis diff_single_trivial diff_union_swap diff_union_swap2 form.distinct(13))
next case OrR thus ?case using SCc.OrR by (metis diff_single_trivial diff_union_swap2 form.distinct(15) insert_iff set_mset_add_mset_insert)
next case ImpL thus ?case using SCc.ImpL by (metis diff_single_trivial diff_union_swap2)
next case ImpR thus ?case using SCc.ImpR by (metis diff_single_trivial diff_union_swap diff_union_swap2 form.distinct(17))
qed (simp_all add: SCc.intros)
lemma Cut_Bot_pre': "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>-{#\<bottom>#}" using Cut_Bot_pre SC_SCp_eq by meson

end
