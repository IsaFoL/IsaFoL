subsubsection\<open>Soundness, Completeness\<close>

theory SC_Sema
imports SC Sema
begin

definition sequent_semantics :: "valuation \<Rightarrow> form multiset \<Rightarrow> form multiset \<Rightarrow> bool" ("(_ \<Turnstile> (_ \<Rightarrow>/ _))" [53, 53,53] 53) where
"\<A> \<Turnstile> \<Gamma> \<Rightarrow> \<Delta> \<equiv> (\<forall>\<gamma> \<in># \<Gamma>. \<A> \<Turnstile> \<gamma>) \<longrightarrow> (\<exists>\<delta> \<in># \<Delta>. \<A> \<Turnstile> \<delta>)"
abbreviation sequent_valid :: "form multiset \<Rightarrow> form multiset \<Rightarrow> bool" ("(\<Turnstile> (_ \<Rightarrow>/ _))" [53,53] 53) where
"\<Turnstile> \<Gamma> \<Rightarrow> \<Delta> \<equiv> \<forall>A. A \<Turnstile> \<Gamma> \<Rightarrow> \<Delta>"
abbreviation sequent_nonvalid :: "valuation \<Rightarrow> form multiset \<Rightarrow> form multiset \<Rightarrow> bool" ("(_ \<not>\<Turnstile> (_ \<Rightarrow>/ _))" [53, 53,53] 53) where
(* Hey, there's an unicode ⊭ and Isabelle doesn't support it? *)
"\<A> \<not>\<Turnstile> \<Gamma> \<Rightarrow> \<Delta> \<equiv> \<not>\<A>\<Turnstile> \<Gamma> \<Rightarrow> \<Delta>"

lemma "\<Turnstile> \<Gamma> \<Rightarrow> \<Delta> \<longleftrightarrow> (\<exists>\<delta>. \<delta> \<in># \<Delta> \<and> set_mset \<Gamma> \<TTurnstile> \<delta>)"
oops text\<open>Mind the order of quantifiers between this and @{const sequent_valid}.\<close>
lemma sequent_intuitonistic_semantics: "\<Turnstile> \<Gamma> \<Rightarrow> {#\<delta>#} \<longleftrightarrow> set_mset \<Gamma> \<TTurnstile> \<delta>"
  unfolding sequent_semantics_def entailment_def by simp

lemma SC_soundness: "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Turnstile> \<Gamma> \<Rightarrow> \<Delta>"
  by(induction rule: SCp.induct) (auto simp add: sequent_semantics_def)

definition "sequent_cost \<Gamma> \<Delta> = Suc (sum_list (sorted_list_of_multiset (image_mset size (\<Gamma> + \<Delta>))))"
lemma SC_completeness: "\<Turnstile> \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta> \<down> sequent_cost \<Gamma> \<Delta>"
proof(induction "sequent_cost \<Gamma> \<Delta>" arbitrary: \<Gamma> \<Delta>)
  case 0 hence False by(simp add: sequent_cost_def) thus ?case by clarify
next
  case (Suc n)
  from Suc(3) show ?case
    using SCc.cases[OF Suc.hyps(1)]
oops
text\<open>Making this proof go through should be possible,
  but finding the right way to split the cases could get verbose.
This is better handled by having Isabelle generate the right splitting rule based on some definition,
  as following.\<close>

function(sequential)
  sc :: "form list \<Rightarrow> nat list \<Rightarrow> form list \<Rightarrow> nat list \<Rightarrow> (nat list \<times> nat list) set" where
"sc [] A [] B = (if set A \<inter> set B = {} then {(A,B)} else {})" |
"sc (\<bottom> # X) A Y B = {}" |
"sc (Atom k # \<Gamma>) A  \<Delta> B = sc \<Gamma> (k#A) \<Delta> B" |
"sc (Not F # X) A Y B = sc X A (F#Y) B" |
"sc (And F G # X) A Y B = sc (F#G#X) A Y B" |
"sc (Or F G # X) A Y B = sc (F#X) A Y B \<union> sc (G#X) A Y B" |
"sc (Imp F G # X) A Y B = sc X A (F#Y) B \<union> sc (G#X) A Y B" |
"sc X A (\<bottom>#Y) B = sc X A Y B" |
"sc X A (Atom k # Y) B = sc X A Y (k#B)" |
"sc X A (Not F # Y) B = sc (F#X) A Y B" |
"sc \<Gamma> A (And F G # \<Delta>) B = sc \<Gamma> A (F#\<Delta>) B \<union> sc \<Gamma> A (G#\<Delta>) B" |
"sc X A (Or F G # Y) B = sc X A (F#G#Y) B" |
"sc X A (Imp F G # Y) B = sc (F#X) A (G#Y) B"
  by pat_completeness auto
(* Paremeters 2 and 4:
   atoms are stored in lists, not sets, simply because lists are automatically
   finite; finiteness is required when we relate back to sequents, which are finite. *)

definition "list_sequent_cost \<Gamma> \<Delta> = 2*sum_list (map size (\<Gamma>@\<Delta>)) + length (\<Gamma>@\<Delta>)"
termination sc by (relation "measure (\<lambda>(X,A,Y,B). list_sequent_cost X Y)") (simp_all add: list_sequent_cost_def)

value(code) "sc [] [] [((Atom 0 \<^bold>\<rightarrow> Atom 1) \<^bold>\<rightarrow> Atom 0) \<^bold>\<rightarrow> Atom 1] []"
  (* yeah, an atom may appear twice in one of the lists, but that is of no concern. 
     Using sets for the atoms stands in the way of automation. *)

lemma sc_sim':
  assumes "sc \<Gamma> G \<Delta> D = {}"
  shows "image_mset Atom (mset G) + mset \<Gamma> \<Rightarrow> image_mset Atom (mset D) + mset \<Delta>"
proof -
  have [simp]: "image_mset Atom (mset A) \<Rightarrow> image_mset Atom (mset B)" (is ?k) if "set A \<inter> set B \<noteq> {}" for A B 
  proof -
    from that obtain a where "a \<in> set A" "a \<in> set B" by blast
    thus ?k by(force simp: in_image_mset intro: SCp.Ax[where k=a])
  qed
  have A: "f A + {# F #} = F, f A" for f and F :: form and A by (simp add: add.commute)
  have B: "f A + (F, g B) = F, f A + g B" for f g and F :: form and A B by (simp add: add.left_commute)
  note C = A B
  note commute_principals_out = C[of mset] C[of "image_mset Atom"]
  note weakenR'[where F=\<bottom>, intro!]
  from assms show ?thesis
    by(induction rule: sc.induct) (auto 
        simp add: list_sequent_cost_def commute_principals_out add.assoc Quickcheck_Exhaustive.orelse_def 
        split: if_splits option.splits 
        intro: SCp.intros(3-))
qed

lemma sc_sim:
  assumes "sc \<Gamma> G \<Delta> D = {}"
  shows "image_mset Atom (mset G) + mset \<Gamma> \<Rightarrow> image_mset Atom (mset D) + mset \<Delta> \<down> list_sequent_cost \<Gamma> \<Delta> + (if set G \<inter> set D = {} then 0 else 1)"
proof -
  have [simp]: "image_mset Atom (mset A) \<Rightarrow> image_mset Atom (mset B) \<down> Suc 0" (is ?k) if "set A \<inter> set B \<noteq> {}" for A B 
  proof -
    from that obtain a where "a \<in> set A" "a \<in> set B" by blast
    thus ?k by(force simp: in_image_mset intro: SCc.Ax[where k=a])
  qed
  have [simp]: "\<bottom>,\<Gamma> \<Rightarrow> \<Delta> \<down> Suc n" for \<Gamma> \<Delta> n by (simp add: SCc.BotL)
  have B: "A + (f F G, B) = f F G, (A + B)" for f and F G :: form and A B :: "form multiset" by (simp add: add.commute union_assoc)
  have A: "f A + {# F #} = F, f A" "f A + (F, g B) = F, f A + g B" for f g and F :: form and A B by (simp_all add: add.left_commute add.commute)
  note commute_principals_out = A[of mset] A[of "image_mset Atom"]
    B[where f=Imp] B[where f=And] B[where f=Or] B[where f="\<lambda>_. Not"]
  note weakenR[where F=\<bottom>, intro!]
  note SCc.intros(3-)[intro]
  have [elim!]: "\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> n \<le> m \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta> \<down> m" for \<Gamma> \<Delta> n m using dec_induct by(fastforce elim!: deeper_suc) (* sledgehammer is flippin' using induction. *)
  from assms show ?thesis
    by(induction \<Gamma> G \<Delta> D rule: sc.induct)
      (fastforce 
      simp add: list_sequent_cost_def commute_principals_out add.assoc Quickcheck_Exhaustive.orelse_def
      split: if_splits option.splits)+
qed

lemma scc_ce_distinct:
  "(C,E) \<in> sc \<Gamma> G \<Delta> D \<Longrightarrow> set C \<inter> set E = {}"
by(induction \<Gamma> G \<Delta> D arbitrary: C E rule: sc.induct)
  (fastforce split: if_splits)+

text\<open>Completeness set aside, this is an interesting fact on the side: Sequent Calculus can provide counterexamples.\<close>
theorem SC_counterexample:
  "(C,E) \<in> sc \<Gamma> G \<Delta> D \<Longrightarrow>
  (\<lambda>a. a \<in> set C) \<not>\<Turnstile> image_mset Atom (mset G) + mset \<Gamma> \<Rightarrow> image_mset Atom (mset D) + mset \<Delta>"
by(induction arbitrary: C E rule: sc.induct; 
   simp add: sequent_semantics_def split: if_splits; 
   (* and just for one last goal\<dots> *) blast)

corollary SC_counterexample':
  assumes "(A,B) \<in> sc \<Gamma> [] \<Delta> []"
  shows "(\<lambda>k. k \<in> set A) \<not>\<Turnstile> mset \<Gamma> \<Rightarrow> mset \<Delta>"
using SC_counterexample[OF assms] by simp

theorem SC_sound_complete: "\<Gamma> \<Rightarrow> \<Delta> \<longleftrightarrow> \<Turnstile> \<Gamma> \<Rightarrow> \<Delta>"
proof
  assume "\<Gamma> \<Rightarrow> \<Delta>" thus "\<Turnstile> \<Gamma> \<Rightarrow> \<Delta>" using SC_soundness by blast
next
  obtain \<Gamma>' \<Delta>' where [simp]: "\<Gamma> = mset  \<Gamma>'" "\<Delta> = mset \<Delta>'" by (metis ex_mset)
  assume "\<Turnstile> \<Gamma> \<Rightarrow> \<Delta>"
  hence "sc \<Gamma>' [] \<Delta>' [] = {}"
  proof(rule contrapos_pp)
    assume "sc \<Gamma>' [] \<Delta>' [] \<noteq> {}"
    then obtain C E where "(C,E) \<in> sc \<Gamma>' [] \<Delta>' []" by fast
    thus "\<not> \<Turnstile> \<Gamma> \<Rightarrow> \<Delta>" using SC_counterexample' by fastforce
  qed
  from sc_sim'[OF this] show "\<Gamma> \<Rightarrow> \<Delta>" by auto
qed
  
theorem "\<Turnstile> mset \<Gamma> \<Rightarrow> mset \<Delta> \<Longrightarrow> mset \<Gamma> \<Rightarrow> mset \<Delta>"
proof cases -- "just to show that we didn't need to show the lemma above by contraposition. It's just quicker to do so."
  assume "sc \<Gamma> [] \<Delta> [] = {}"
  from sc_sim'[OF this] show ?thesis  by auto
next
  assume "sc \<Gamma> [] \<Delta> [] \<noteq> {}"
  with SC_counterexample have "\<not> \<Turnstile> mset \<Gamma> \<Rightarrow> mset \<Delta>" by fastforce
  moreover assume "\<Turnstile> mset \<Gamma> \<Rightarrow> mset \<Delta>"
  ultimately have False ..
  thus ?thesis ..
qed
  
end
