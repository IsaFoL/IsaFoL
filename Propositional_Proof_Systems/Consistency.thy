subsection\<open>Consistency\<close>

text\<open>We follow the proofs by Melvin Fitting~\cite{fitting1990first}.\<close>
theory Consistency
imports Sema
begin

definition "Hintikka S \<equiv> (
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
\<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
\<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
\<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)
)"

lemma "Hintikka {Atom 0 \<^bold>\<and> ((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), ((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), Atom 0, \<^bold>\<not>(\<^bold>\<not> (Atom 1)), Atom 1}"
  unfolding Hintikka_def by simp

theorem Hintikkas_lemma:
  assumes H: "Hintikka S"
  shows "sat S"
proof -
  from H[unfolded Hintikka_def]
  have H': "\<bottom> \<notin> S" 
    "Atom k \<in> S \<Longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<Longrightarrow> False"
    "F \<^bold>\<and> G \<in> S \<Longrightarrow> F \<in> S \<and> G \<in> S"
    "F \<^bold>\<or> G \<in> S \<Longrightarrow> F \<in> S \<or> G \<in> S"
    "F \<^bold>\<rightarrow> G \<in> S \<Longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S"
    "\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<Longrightarrow> F \<in> S"
    "\<^bold>\<not> (F \<^bold>\<and> G) \<in> S \<Longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
    "\<^bold>\<not> (F \<^bold>\<or> G) \<in> S \<Longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    "\<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<Longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    for k F G by blast+
  let ?M = "\<lambda>k. Atom k \<in> S"
  have "(F \<in> S \<longrightarrow> (?M \<Turnstile> F)) \<and> (\<^bold>\<not> F \<in> S \<longrightarrow> (\<not>(?M \<Turnstile> F)))" for F
    by(induction F) (auto simp: H'(1) dest!: H'(2-))
  thus ?thesis unfolding sat_def by blast
qed

definition "pcp C \<equiv> (\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<cdot> G \<cdot> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<cdot> S \<in> C \<or> G \<cdot> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<cdot> S \<in> C \<or> G \<cdot> S \<in> C)
\<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<cdot> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<cdot> S \<in> C \<or> \<^bold>\<not> G \<cdot> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<cdot> \<^bold>\<not> G \<cdot> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<cdot> \<^bold>\<not> G \<cdot> S \<in> C)
)"

(* just some funny examples *)
lemma "pcp {}" "pcp {{}}" "pcp {{Atom 0}}" by (simp add: pcp_def)+
lemma "pcp {{(\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2},
   {((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), \<^bold>\<not>(\<^bold>\<not> (Atom 1))},
  {((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), \<^bold>\<not>(\<^bold>\<not> (Atom 1)),  Atom 1}}" by (auto simp add: pcp_def)
  
definition "subset_closed C \<equiv> (\<forall>S \<in> C. \<forall>s\<subseteq>S. s \<in> C)"
definition "finite_character C \<equiv> (\<forall>S. S \<in> C \<longleftrightarrow> (\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C))"

lemma ex1: "pcp C \<Longrightarrow> \<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> subset_closed C'"
proof(intro exI[of _ "{s . \<exists>S \<in> C. s \<subseteq> S}"] conjI)
  let ?E = "{s. \<exists>S\<in>C. s \<subseteq> S}"
  show "C \<subseteq> ?E" by blast
  show "subset_closed ?E" unfolding subset_closed_def by blast
  assume C: \<open>pcp C\<close>
  show "pcp ?E" using C  unfolding pcp_def
    by (intro ballI conjI; unfold mem_Collect_eq; 
        metis Un_insert_left set_rev_mp subset_Un_eq sup_ge1)
qed

lemma sallI: "(\<And>s. s \<subseteq> S \<Longrightarrow> P s) \<Longrightarrow> \<forall>s \<subseteq> S. P s" by simp 

lemma ex2: 
  assumes fc: "finite_character C"
  shows "subset_closed C"
  unfolding subset_closed_def
proof (intro ballI sallI)
  fix s S
  assume e: \<open>S \<in> C\<close> and s: \<open>s \<subseteq> S\<close>
  hence *: "t \<subseteq> s \<Longrightarrow> t \<subseteq> S" for t by simp
  from fc have "t \<subseteq> S \<Longrightarrow> finite t \<Longrightarrow> t \<in> C" for t unfolding finite_character_def using e by blast
  hence "t \<subseteq> s \<Longrightarrow> finite t \<Longrightarrow> t \<in> C" for t using * by simp
  with fc show \<open>s \<in> C\<close> unfolding finite_character_def by blast
qed
  
(*inductive_set
  finite_pcp :: "form set set \<Rightarrow> form set set"
  for C :: "form set set"
where
  "S \<in> C \<Longrightarrow> S \<in> finite_pcp C" |
  "\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> finite_pcp C \<Longrightarrow> S \<in> finite_pcp C" |
  "F \<^bold>\<and> G \<in> S \<Longrightarrow> S \<in> finite_pcp C \<Longrightarrow> F \<cdot> G \<cdot> S \<in> finite_pcp C" |
  "F \<^bold>\<or> G \<in> S \<Longrightarrow> S \<in> finite_pcp C \<Longrightarrow> F \<cdot> S \<in> finite_pcp C \<or> G \<cdot> S \<in> finite_pcp C" |
  "F \<^bold>\<rightarrow> G \<in> S \<Longrightarrow> S \<in> finite_pcp C \<Longrightarrow> \<^bold>\<not>F \<cdot> S \<in> finite_pcp C \<or> G \<cdot> S \<in> finite_pcp C" |
  "\<^bold>\<not> (\<^bold>\<not>F) \<in> S \<Longrightarrow> S \<in> finite_pcp C \<Longrightarrow> F \<cdot> S \<in> finite_pcp C" |
  "\<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<Longrightarrow> S \<in> finite_pcp C \<Longrightarrow> \<^bold>\<not> F \<cdot> S \<in> finite_pcp C \<or> \<^bold>\<not> G \<cdot> S \<in> finite_pcp C" |
  "\<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<Longrightarrow> S \<in> finite_pcp C \<Longrightarrow> \<^bold>\<not> F \<cdot> \<^bold>\<not> G \<cdot> S \<in> finite_pcp C" |
  "\<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<Longrightarrow> S \<in> finite_pcp C \<Longrightarrow> F \<cdot> \<^bold>\<not> G \<cdot> S \<in> finite_pcp C"*)
    
lemma ex3: "pcp C \<Longrightarrow> subset_closed C \<Longrightarrow> \<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> finite_character C'"
proof(intro exI[of _ "C \<union> {S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"] conjI)
  let ?E = " {S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"
  show "C \<subseteq> C \<union> ?E" by blast
  assume S: \<open>subset_closed C\<close>
  thus "finite_character (C \<union> ?E)" unfolding finite_character_def subset_closed_def by blast
  assume C: \<open>pcp C\<close>
  note C' = C[unfolded pcp_def, THEN bspec]
  
  have disj: "\<And>f2 g2 h2 F2 G2 S2. \<lbrakk>\<And>s. \<lbrakk>s \<in> C; h2 F2 G2 \<in> s\<rbrakk> \<Longrightarrow> f2 F2 \<cdot> s \<in> C \<or> g2 G2 \<cdot> s \<in> C; \<forall>s\<subseteq>S2. finite s \<longrightarrow> s \<in> C; h2 F2 G2 \<in> S2\<rbrakk>
      \<Longrightarrow> f2 F2 \<cdot> S2 \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C} \<or> g2 G2 \<cdot> S2 \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}" proof -
    fix F G :: form fix S fix f g :: "form \<Rightarrow> form" and h :: "form \<Rightarrow> form \<Rightarrow> form"
    let ?H = "h (f F) (g G)" (* this also works with "h F G". I have no clue what that means. probably that qed does some more magic so it doesn't matter which you use *)
    let ?F = "f F"  let ?G = "g G"
    (* this proof is probably too complicated for what it's doing anyway. I invite you to fix it. *)
    assume C': \<open>\<And>s. s \<in> C \<Longrightarrow> ?H \<in> s \<Longrightarrow> ?F \<cdot> s \<in> C \<or> ?G \<cdot> s \<in> C\<close>
    assume si: \<open>\<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C\<close>
    have l: "\<exists>I\<in>{?F,?G}. I \<cdot> s1 \<in> C \<and> I \<cdot> s2 \<in> C" 
      if "s1 \<subseteq> S" "finite s1" "?H \<in> s1" 
         "s2 \<subseteq> S" "finite s2" "?H \<in> s2" for s1 s2
    proof -
      let ?s = "s1 \<union> s2"
      have "?s \<subseteq> S" "finite ?s" using that by simp_all 
      with si have "?s \<in> C" by simp
      moreover have "?H \<in> ?s" using that by simp
      ultimately have "\<exists>I\<in>{?F,?G}. I \<cdot> ?s \<in> C"
        using C' by simp
      thus "\<exists>I\<in>{?F,?G}. I \<cdot> s1 \<in> C \<and> I \<cdot> s2 \<in> C"
        by (meson S[unfolded subset_closed_def, THEN bspec] insert_mono sup.cobounded2 sup_ge1)
    qed
    have m: "\<lbrakk>s1 \<subseteq> S; finite s1; ?H \<in> s1; ?F \<cdot> s1 \<notin> C; s2 \<subseteq> S; finite s2; ?H \<in> s2; ?G \<cdot> s2 \<notin> C\<rbrakk> \<Longrightarrow> False" for s1 s2
      using l by blast
    assume a: \<open>?H \<in> S\<close>
    have "False" if "s1 \<subseteq> S" "finite s1" "?F \<cdot> s1 \<notin> C" "s2 \<subseteq> S" "finite s2" "?G \<cdot> s2 \<notin> C" for s1 s2
    proof -
      have *: "?H \<cdot> s1 \<subseteq> S" "finite (?H \<cdot> s1)" "?H \<in> ?H \<cdot> s1" if  "s1 \<subseteq> S" "finite s1" for s1
        using that a by simp_all
      have  "?F \<cdot> ?H \<cdot> s1 \<notin> C" "?G \<cdot> ?H \<cdot> s2 \<notin> C" 
        by (meson S insert_mono subset_closed_def subset_insertI that(3,6))+
      from m[OF *[OF that(1-2)] this(1) *[OF that(4-5)] this(2)]
      show False .
    qed
    hence "?F \<cdot> S \<in> ?E \<or> ?G \<cdot> S \<in> ?E"
      unfolding mem_Collect_eq Un_iff (* sledgehammering here makes for the most complicated isar proof I've ever seen generated *)
      by (metis finite_Diff insert_Diff si subset_insert_iff)
    thus "?F \<cdot> S \<in> C \<union> ?E \<or> ?G \<cdot> S \<in> C \<union> ?E" by blast
  qed
    
  have conj: "\<And>f3 g3 h3 F3 G3 S3. \<lbrakk>\<And>s. \<lbrakk>s \<in> C; h3 F3 G3 \<in> s\<rbrakk> \<Longrightarrow> f3 F3 \<cdot> g3 G3 \<cdot> s \<in> C;
    \<forall>s\<subseteq>S3. finite s \<longrightarrow> s \<in> C; h3 F3 G3 \<in> S3\<rbrakk> \<Longrightarrow> f3 F3 \<cdot> g3 G3 \<cdot> S3 \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}" proof -
    fix F G :: form fix S fix f g :: "form \<Rightarrow> form" and h :: "form \<Rightarrow> form \<Rightarrow> form"
    let ?H = "h F G" let ?F = "f F"  let ?G = "g G"
    assume C': \<open>\<And>s. s \<in> C \<Longrightarrow> ?H \<in> s \<Longrightarrow> ?F \<cdot> ?G \<cdot> s \<in> C\<close>
    assume si: \<open>\<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C\<close>
    hence k: "\<forall>s \<subseteq> S. finite s \<longrightarrow> ?H \<in> s \<longrightarrow> ?F \<cdot> ?G \<cdot> s \<in> C"
      using C' by simp
    assume a: \<open>?H \<in> S\<close>
    have "?F \<cdot> ?G \<cdot> S \<in> ?E"
      unfolding mem_Collect_eq Un_iff proof safe
      fix s
      assume "s \<subseteq> ?F \<cdot> ?G \<cdot> S" and f: "finite s"
      hence "?H \<cdot> (s - {?F,?G}) \<subseteq> S" using a by blast
      with k f have "?F \<cdot> ?G \<cdot> ?H \<cdot> (s - {?F,?G}) \<in> C" by simp
      hence "?H \<cdot> ?F \<cdot> ?G \<cdot> s \<in> C" using insert_absorb by fastforce
      thus "s \<in> C" using S unfolding subset_closed_def by fast  
    qed
    thus "?F \<cdot> ?G \<cdot> S \<in> C \<union> ?E" by simp
  qed
  
  show "pcp (C \<union> ?E)" unfolding pcp_def
    apply(intro ballI conjI; elim UnE; (unfold mem_Collect_eq)?)
    subgoal using C' by blast
    subgoal using C' by blast
    subgoal using C' by (simp;fail)
    subgoal by (meson C' empty_subsetI finite.emptyI finite_insert insert_subset subset_insertI)
    (*subgoal proof - (* sledgehammer doesn't find this anymore, so I want to keep it around in case the meson proof fails. *)
      fix S :: "form set"
      assume a1: "\<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C"
      { fix nn :: nat
        obtain bb :: "form set \<Rightarrow> bool" where
            ff1: "\<forall>X1. bb X1 = (\<bottom> \<notin> X1 \<and> (\<forall>x. Atom x \<in> X1 \<longrightarrow> \<^bold>\<not> (Atom x) \<notin> X1) \<and> (\<forall>X3 X4. X3 \<^bold>\<and> X4 \<in> X1 \<longrightarrow> X3 \<cdot> X4 \<cdot> X1 \<in> C) \<and> (\<forall>X3 X4. X3 \<^bold>\<or> X4 \<in> X1 \<longrightarrow> X3 \<cdot> X1 \<in> C \<or> X4 \<cdot> X1 \<in> C) \<and> (\<forall>X3 X4. X3 \<^bold>\<rightarrow> X4 \<in> X1 \<longrightarrow> \<^bold>\<not> X3 \<cdot> X1 \<in> C \<or> X4 \<cdot> X1 \<in> C) \<and> (\<forall>X3. \<^bold>\<not> (\<^bold>\<not> X3) \<in> X1 \<longrightarrow> X3 \<cdot> X1 \<in> C) \<and> (\<forall>X3 X4. \<^bold>\<not> (X3 \<^bold>\<and> X4) \<in> X1 \<longrightarrow> \<^bold>\<not> X3 \<cdot> X1 \<in> C \<or> \<^bold>\<not> X4 \<cdot> X1 \<in> C) \<and> (\<forall>X3 X4. \<^bold>\<not> (X3 \<^bold>\<or> X4) \<in> X1 \<longrightarrow> \<^bold>\<not> X3 \<cdot> \<^bold>\<not> X4 \<cdot> X1 \<in> C) \<and> (\<forall>X3 X4. \<^bold>\<not> (X3 \<^bold>\<rightarrow> X4) \<in> X1 \<longrightarrow> X3 \<cdot> \<^bold>\<not> X4 \<cdot> X1 \<in> C))"
          by moura
        then have ff2: "\<forall>F. F \<in> C \<longrightarrow> bb F"
          using C' by auto
        have "\<not> bb {Atom nn, \<^bold>\<not> (Atom nn)}"
          using ff1 by simp
        then have "Atom nn \<notin> S \<or> \<^bold>\<not> (Atom nn) \<notin> S"
          using ff2 a1 by (meson empty_subsetI finite.emptyI finite_insert insert_subset) }
      then show "\<forall>n. Atom n \<in> S \<longrightarrow> \<^bold>\<not> (Atom n) \<in> S \<longrightarrow> False"
        by blast
    qed *)
    subgoal using C' by simp
    apply(intro allI impI) subgoal for S F G using conj[of And F G "\<lambda>k. k" "\<lambda>k. k" S] C' by simp
    subgoal using C' by fast
    apply(intro allI impI) subgoal for S F G using disj[of Or F G "\<lambda>k. k" "\<lambda>k. k" S] C' by simp
    subgoal using C' by fast
    apply(intro allI impI) subgoal for S F G using disj[of Imp F G Not "\<lambda>k. k" S] C' by simp
    subgoal using C' by fast
    apply(intro allI impI) subgoal for S F using conj[of "\<lambda>F G. Not (Not F)" F F "\<lambda>k. k" "\<lambda>k. k" S] C' 
        (* wow, gross misuse of the claims - disj instead of conj also works *) by simp
    subgoal using C' by fast
    apply(intro allI impI) subgoal for S F G using disj[of "\<lambda>F G. Not (And F G)" F G Not Not S] C' by simp
    subgoal using C' by blast
    apply(intro allI impI) subgoal for S F G using conj[of "\<lambda>F G. Not (Or F G)" F G Not Not S] C' by simp
    subgoal using C' by blast
    apply(intro allI impI) subgoal for S F G using conj[of "\<lambda>F G. Not (Imp F G)" F G "\<lambda>k. k" Not S] C' by simp
  done
qed

primrec pcp_seq where
"pcp_seq C S 0 = S" |
"pcp_seq C S (Suc n) = (
  let Sn = pcp_seq C S n; Sn1 = from_nat n \<cdot> Sn in
  if Sn1 \<in> C then Sn1 else Sn
)"

lemma pcp_seq_in: "pcp C \<Longrightarrow> S \<in> C \<Longrightarrow> pcp_seq C S n \<in> C"
proof(induction n)
  case (Suc n)
  hence "pcp_seq C S n \<in> C" by simp
  thus ?case by(simp add: Let_def)
qed simp
  
lemma pcp_seq_mono: "n \<le> m \<Longrightarrow> pcp_seq C S n \<subseteq> pcp_seq C S m"
proof(induction m)
  case (Suc m)
  thus ?case by(cases "n = Suc m"; simp add: Let_def; blast)
qed simp

lemma pcp_seq_UN: "\<Union>{pcp_seq C S n|n. n \<le> m} = pcp_seq C S m"
proof(induction m)
  case (Suc m)
  have "{f n |n. n \<le> Suc m} = f (Suc m) \<cdot> {f n |n. n \<le> m}" for f using le_Suc_eq by auto
  hence "{pcp_seq C S n |n. n \<le> Suc m} = pcp_seq C S (Suc m) \<cdot> {pcp_seq C S n |n. n \<le> m}" .
  hence "\<Union>{pcp_seq C S n |n. n \<le> Suc m} = \<Union>{pcp_seq C S n |n. n \<le> m} \<union> pcp_seq C S (Suc m)" by auto
  thus ?case using Suc pcp_seq_mono by blast
qed simp
  
lemma wont_get_added: "(F :: form) \<notin> pcp_seq C S (Suc (to_nat F)) \<Longrightarrow> F \<notin> pcp_seq C S (Suc (to_nat F) + n)"
text\<open>We don't necessarily have @{term "n = to_nat (from_nat n)"}, so this doesn't hold.\<close>
oops

definition "pcp_lim C S \<equiv> \<Union>{pcp_seq C S n|n. True}"
  
lemma pcp_seq_sub: "pcp_seq C S n \<subseteq> pcp_lim C S"
  unfolding pcp_lim_def by(induction n; blast)
    
lemma pcp_lim_inserted_at_ex: "x \<in> pcp_lim C S \<Longrightarrow> \<exists>k. x \<in> pcp_seq C S k"
  unfolding pcp_lim_def by blast

lemma pcp_lim_in:
  assumes c: "pcp C"
  and el: "S \<in> C"
  and sc: "subset_closed C"
  and fc: "finite_character C"
  shows "pcp_lim C S \<in> C" (is "?cl \<in> C")
proof -
  from pcp_seq_in[OF c el, THEN allI] have "\<forall>n. pcp_seq C S n \<in> C" .
  hence "\<forall>m. \<Union>{pcp_seq C S n|n. n \<le> m} \<in> C" unfolding pcp_seq_UN .
  
  have "\<forall>s \<subseteq> ?cl. finite s \<longrightarrow> s \<in> C"
  proof safe
    fix s :: "form set"
    have "pcp_seq C S (Suc (Max (to_nat ` s))) \<subseteq> pcp_lim C S" using pcp_seq_sub by blast
    assume \<open>finite s\<close> \<open>s \<subseteq> pcp_lim C S\<close>
    hence "\<exists>k. s \<subseteq> pcp_seq C S k" 
    proof(induction s rule: finite_induct) 
      case (insert x s)
      hence "\<exists>k. s \<subseteq> pcp_seq C S k" by fast
      then guess k1 ..
      moreover obtain k2 where "x \<in> pcp_seq C S k2"
        by (meson pcp_lim_inserted_at_ex insert.prems insert_subset)
      ultimately have "x \<cdot> s \<subseteq> pcp_seq C S (max k1 k2)"
        by (meson pcp_seq_mono dual_order.trans insert_subset max.bounded_iff order_refl subsetCE)
      thus ?case by blast
    qed simp
    with pcp_seq_in[OF c el] sc
    show "s \<in> C" unfolding subset_closed_def by blast
  qed
  thus "?cl \<in> C" using fc unfolding finite_character_def by blast
qed
  
lemma cl_max:
  assumes c: "pcp C"
  assumes sc: "subset_closed C"
  assumes el: "K \<in> C"
  assumes su: "pcp_lim C S \<subseteq> K"
  shows "pcp_lim C S = K" (is ?e)
proof (rule ccontr)
  assume \<open>\<not>?e\<close>
  with su have "pcp_lim C S \<subset> K" by simp
  then obtain F where e: "F \<in> K" and ne: "F \<notin> pcp_lim C S" by blast
  from ne have "F \<notin> pcp_seq C S (Suc (to_nat F))" using pcp_seq_sub by fast
  hence 1: "F \<cdot> pcp_seq C S (to_nat F) \<notin> C" by (simp add: Let_def split: if_splits)
  have "F \<cdot> pcp_seq C S (to_nat F) \<subseteq> K" using pcp_seq_sub e su by blast
  hence "F \<cdot> pcp_seq C S (to_nat F) \<in> C" using sc unfolding subset_closed_def using el by blast
  with 1 show False ..
qed

lemma cl_max':
  assumes c: "pcp C"
  assumes sc: "subset_closed C"
  shows "F \<cdot> pcp_lim C S \<in> C \<Longrightarrow> F \<in> pcp_lim C S"
    "F \<cdot> G \<cdot> pcp_lim C S \<in> C \<Longrightarrow> F \<in> pcp_lim C S \<and> G \<in> pcp_lim C S"
using cl_max[OF assms] by blast+

lemma pcp_lim_Hintikka:
  assumes c: "pcp C"
  assumes sc: "subset_closed C"
  assumes fc: "finite_character C"
  assumes el: "S \<in> C"
  shows "Hintikka (pcp_lim C S)"
proof -
  let ?cl = "pcp_lim C S"
  have "?cl \<in> C" using pcp_lim_in[OF c el sc fc] .
  from c[unfolded pcp_def, THEN bspec, OF this]
  have d: "\<bottom> \<notin> ?cl"
    "Atom k \<in> ?cl \<Longrightarrow> \<^bold>\<not> (Atom k) \<in> ?cl \<Longrightarrow> False"
    "F \<^bold>\<and> G \<in> ?cl \<Longrightarrow> F \<cdot> G \<cdot> ?cl \<in> C"
    "F \<^bold>\<or> G \<in> ?cl \<Longrightarrow> F \<cdot> ?cl \<in> C \<or> G \<cdot> ?cl \<in> C"
    "F \<^bold>\<rightarrow> G \<in> ?cl \<Longrightarrow> \<^bold>\<not> F \<cdot> ?cl \<in> C \<or> G \<cdot> ?cl \<in> C"
    "\<^bold>\<not> (\<^bold>\<not> F) \<in> ?cl \<Longrightarrow> F \<cdot> ?cl \<in> C"
    "\<^bold>\<not> (F \<^bold>\<and> G) \<in> ?cl \<Longrightarrow> \<^bold>\<not> F \<cdot> ?cl \<in> C \<or> \<^bold>\<not> G \<cdot> ?cl \<in> C"
    "\<^bold>\<not> (F \<^bold>\<or> G) \<in> ?cl \<Longrightarrow> \<^bold>\<not> F \<cdot> \<^bold>\<not> G \<cdot> ?cl \<in> C"
    "\<^bold>\<not> (F \<^bold>\<rightarrow> G) \<in> ?cl \<Longrightarrow> F \<cdot> \<^bold>\<not> G \<cdot> ?cl \<in> C"
  for k F G by blast+
  have
    "F \<^bold>\<and> G \<in> ?cl \<Longrightarrow> F \<in> ?cl \<and> G \<in> ?cl"
    "F \<^bold>\<or> G \<in> ?cl \<Longrightarrow> F \<in> ?cl \<or> G \<in> ?cl"
    "F \<^bold>\<rightarrow> G \<in> ?cl \<Longrightarrow> \<^bold>\<not> F \<in> ?cl \<or> G \<in> ?cl"
    "\<^bold>\<not> (\<^bold>\<not> F) \<in> ?cl \<Longrightarrow> F \<in> ?cl"
    "\<^bold>\<not> (F \<^bold>\<and> G) \<in> ?cl \<Longrightarrow> \<^bold>\<not> F \<in> ?cl \<or> \<^bold>\<not> G \<in> ?cl"
    "\<^bold>\<not> (F \<^bold>\<or> G) \<in> ?cl \<Longrightarrow> \<^bold>\<not> F \<in> ?cl \<and> \<^bold>\<not> G \<in> ?cl"
    "\<^bold>\<not> (F \<^bold>\<rightarrow> G) \<in> ?cl \<Longrightarrow> F \<in> ?cl \<and> \<^bold>\<not> G \<in> ?cl"
    for k F G
    by(auto dest: d(3-) cl_max'[OF c sc])
  with d(1,2) show ?thesis unfolding Hintikka_def by fast
qed
  
theorem pcp_sat: -- "model existence theorem"
  assumes c: "pcp C"
  assumes el: "S \<in> C"
  shows "sat S"
proof -
  from c obtain Ce where "C \<subseteq> Ce" "pcp Ce" "subset_closed Ce" "finite_character Ce" using ex1 ex2 ex3 by (metis order_trans)
  have "S \<in> Ce" using \<open>C \<subseteq> Ce\<close> el ..
  with pcp_lim_Hintikka \<open>pcp Ce\<close> \<open>subset_closed Ce\<close> \<open>finite_character Ce\<close>
  have  "Hintikka (pcp_lim Ce S)" .
  with Hintikkas_lemma have "sat (pcp_lim Ce S)" .
  moreover have "S \<subseteq> pcp_lim Ce S" using pcp_seq.simps(1) pcp_seq_sub by fast
  ultimately show ?thesis unfolding sat_def by fast
qed
(* This and Hintikka's lemma are the only two where we need semantics. 
   Still, I don't think it's meaningful to separate those two into an extra theory. *)


end