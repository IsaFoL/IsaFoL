subsection\<open>Hilbert Calculus\<close>
theory HC
imports Formulas
begin

text\<open>We can define Hilbert Calculus as the modus ponens closure over a set of axioms:\<close>
inductive HC :: "form set \<Rightarrow> form \<Rightarrow> bool" (infix "\<turnstile>\<^sub>H" 30) for \<Gamma> :: "form set" where
Ax: "F \<in> \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>H F" |
MP: "\<Gamma> \<turnstile>\<^sub>H F \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>H F \<^bold>\<rightarrow> G \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>H G"
text\<open>.\<close>

context begin

(* 
private abbreviation HC_short (infix "\<turnstile>\<^sub>H" 30)
where "ax \<turnstile>\<^sub>H F \<equiv> ax \<turnstile>\<^sub>H\<^sub>H F"
Feature request!11
*)

text\<open>The problem with that is defining the axioms. Normally, we just write that @{term "F \<^bold>\<rightarrow> (G \<^bold>\<rightarrow> F)"} is an axiom, 
  and mean that anything can be substituted for @{term F} and @{term G}.
Now, we can't just write down a set \<open>{F \<^bold>\<rightarrow> (G \<^bold>\<rightarrow> F), \dots\<close>.
Instead, defining it as an inductive set with no induction is a good idea.
\<close>
(* Note to self: Don't try to formulate these as a definition. Possible, but painful to use. *)
inductive_set AX0 where
"F \<^bold>\<rightarrow> (G \<^bold>\<rightarrow> F) \<in> AX0" |
"(F \<^bold>\<rightarrow> (G \<^bold>\<rightarrow> H)) \<^bold>\<rightarrow> ((F \<^bold>\<rightarrow> G) \<^bold>\<rightarrow> (F \<^bold>\<rightarrow> H)) \<in> AX0"
inductive_set AX10 where
"F \<in> AX0 \<Longrightarrow> F \<in> AX10" |
"F \<^bold>\<rightarrow> (F \<^bold>\<or> G) \<in> AX10" |
"G \<^bold>\<rightarrow> (F \<^bold>\<or> G) \<in> AX10" |
"(F \<^bold>\<rightarrow> H) \<^bold>\<rightarrow> ((G \<^bold>\<rightarrow> H) \<^bold>\<rightarrow> ((F \<^bold>\<or> G) \<^bold>\<rightarrow> H)) \<in> AX10" |
"(F \<^bold>\<and> G) \<^bold>\<rightarrow> F \<in> AX10" | 
"(F \<^bold>\<and> G) \<^bold>\<rightarrow> G \<in> AX10" |
"F \<^bold>\<rightarrow> (G \<^bold>\<rightarrow> (F \<^bold>\<and> G)) \<in> AX10" |
"(F \<^bold>\<rightarrow> \<bottom>) \<^bold>\<rightarrow> \<^bold>\<not>F \<in> AX10" |
"\<^bold>\<not>F \<^bold>\<rightarrow> (F \<^bold>\<rightarrow> \<bottom>) \<in> AX10" |
"(\<^bold>\<not>F \<^bold>\<rightarrow> \<bottom>) \<^bold>\<rightarrow> F \<in> AX10"
lemmas HC_intros[intro!] = 
  AX0.intros[THEN HC.intros(1)]
  AX0.intros[THEN AX10.intros(1), THEN HC.intros(1)]
  AX10.intros(2-)[THEN HC.intros(1)]

inductive_set AXH where
  "(F \<^bold>\<rightarrow> (G \<^bold>\<rightarrow> F)) \<in> AXH" |
  "(F \<^bold>\<rightarrow> (F \<^bold>\<rightarrow> G)) \<^bold>\<rightarrow> (F \<^bold>\<rightarrow> G) \<in> AXH" |
  "(F \<^bold>\<rightarrow> (G \<^bold>\<rightarrow> H)) \<^bold>\<rightarrow> (G \<^bold>\<rightarrow> (F \<^bold>\<rightarrow> H)) \<in> AXH" |
  "(G \<^bold>\<rightarrow> H) \<^bold>\<rightarrow> ((F \<^bold>\<rightarrow> G) \<^bold>\<rightarrow> (F \<^bold>\<rightarrow> H)) \<in> AXH"

lemma HC_mono: "S \<turnstile>\<^sub>H F \<Longrightarrow> S \<subseteq> T \<Longrightarrow> T \<turnstile>\<^sub>H F"
  by(induction rule: HC.induct) (auto intro: HC.intros)
lemma AX010: "AX0 \<subseteq> AX10"
  apply(rule)
  apply(cases rule: AX0.cases, assumption)
   apply(auto intro: AX10.intros)
done
lemma AX100[simp]: "AX0 \<union> AX10 = AX10" using AX010 by blast

text\<open>Hilbert~\cite{hilbert1928grundlagen} formulates his first four axioms quite a bit differently.
  In the end, it doesn't really matter:\<close>
lemma hilbert_folgeaxiome_as_strong_as_AX0: "AX0 \<union> \<Gamma> \<turnstile>\<^sub>H F \<longleftrightarrow> AXH  \<union> \<Gamma> \<turnstile>\<^sub>H F"
proof -
  have 0:
  "AX0 \<turnstile>\<^sub>H (A \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> B)"
  "AX0 \<turnstile>\<^sub>H (A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> C)) \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> C))"
  "AX0 \<turnstile>\<^sub>H (B \<^bold>\<rightarrow> C) \<^bold>\<rightarrow> ((A \<^bold>\<rightarrow> B) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> C))" 
    for A B C using HC_intros(1,2) MP by metis+
  have H:
    "AXH \<turnstile>\<^sub>H (A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> C)) \<^bold>\<rightarrow> ((A \<^bold>\<rightarrow> B) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> C))"
    for A B C
  proof -
    note AXH.intros[THEN HC.Ax]
    thus ?thesis using MP by meson
  qed
  note * = H 0
  note * = *[THEN HC_mono, OF Un_upper1]
  show ?thesis (is "?Z \<longleftrightarrow> ?H") (* HC, where nothing is automatic (except for after this, nearly everything is) *)
  proof
    assume ?Z thus ?H proof induction
      case MP thus ?case using HC.MP by blast
    next
      case (Ax F) thus ?case proof
        assume "F \<in> AX0" thus ?thesis by induction (simp_all add: AXH.intros(1) HC.Ax *)
      next
        assume "F \<in> \<Gamma>" thus ?case using HC.Ax by simp
      qed
    qed
  next
    assume ?H thus ?Z proof induction
      case MP thus ?case using HC.MP by blast
    next
      case (Ax F) thus ?case proof
        assume "F \<in> AXH" thus ?thesis by induction (simp_all add: AX0.intros(1) HC.Ax *)
      next
        assume "F \<in> \<Gamma>" thus ?case using HC.Ax by simp
      qed
    qed
  qed
qed

lemma "AX0 \<turnstile>\<^sub>H F \<^bold>\<rightarrow> F" by (meson HC_intros(1,2) HC.MP)
(* Can you do that again, but slowly? *)
lemma imp_self: "AX0 \<turnstile>\<^sub>H A \<^bold>\<rightarrow> A" proof -
  let ?d = "\<lambda>f. AX0 \<turnstile>\<^sub>H f"
  note MP
  moreover have "?d (A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A))" for B using HC_intros(1)[where G=B and F=A] .
  moreover {
    note MP
    moreover have "?d (A \<^bold>\<rightarrow> ((B \<^bold>\<rightarrow> A) \<^bold>\<rightarrow> A))" for B using HC_intros(1)[where G="B \<^bold>\<rightarrow> A" and F=A] .
    moreover have "?d ((A \<^bold>\<rightarrow> ((B \<^bold>\<rightarrow> A) \<^bold>\<rightarrow> A)) \<^bold>\<rightarrow> ((A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A)) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> A)))" for B using HC_intros(2)[where G="B \<^bold>\<rightarrow> A" and F=A and H=A] .
    ultimately have "?d ((A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A)) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> A))" for B . }
  ultimately show "?d (A \<^bold>\<rightarrow> A)" .
qed

(* quite natural, you'd get the idea for this theorem just when writing the HCND proof. *)
theorem Deduction_theorem: "AX0 \<union> insert F \<Gamma> \<turnstile>\<^sub>H G \<Longrightarrow> AX0 \<union> \<Gamma> \<turnstile>\<^sub>H F \<^bold>\<rightarrow> G"
proof(induction rule: HC.induct)
  case (Ax G)
  show ?case proof cases
    assume "F = G"
    from imp_self have "AX0 \<turnstile>\<^sub>H G \<^bold>\<rightarrow> G" .
    with HC_mono show ?case unfolding \<open>F = G\<close> using sup_ge1 .
  next
    assume "F \<noteq> G"
    note HC.MP
    moreover {
      from \<open>F \<noteq> G\<close> \<open>G \<in> AX0 \<union> insert F \<Gamma>\<close> have "G \<in> AX0 \<union> \<Gamma>" by simp
      with HC.Ax have "AX0 \<union> \<Gamma> \<turnstile>\<^sub>H G" .
    }
    moreover from HC_mono[OF HC_intros(1) sup_ge1] have "AX0 \<union> \<Gamma> \<turnstile>\<^sub>H G \<^bold>\<rightarrow> (F \<^bold>\<rightarrow> G)" .
    ultimately show ?case .
  qed
next
  case (MP G H)
  have "AX0 \<union> \<Gamma> \<turnstile>\<^sub>H (F \<^bold>\<rightarrow> (G \<^bold>\<rightarrow> H)) \<^bold>\<rightarrow> ((F \<^bold>\<rightarrow> G) \<^bold>\<rightarrow> (F \<^bold>\<rightarrow> H))" using HC_mono by blast
  with HC.MP \<open>AX0 \<union> \<Gamma> \<turnstile>\<^sub>H F \<^bold>\<rightarrow> (G \<^bold>\<rightarrow> H)\<close> have "AX0 \<union> \<Gamma> \<turnstile>\<^sub>H (F \<^bold>\<rightarrow> G) \<^bold>\<rightarrow> (F \<^bold>\<rightarrow> H)" .
  with HC.MP \<open>AX0 \<union> \<Gamma> \<turnstile>\<^sub>H F \<^bold>\<rightarrow> G\<close> show "AX0 \<union> \<Gamma> \<turnstile>\<^sub>H F \<^bold>\<rightarrow> H" .
qed


end

end

