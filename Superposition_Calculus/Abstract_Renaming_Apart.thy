theory Abstract_Renaming_Apart
  imports
    Main
    "HOL-Library.Char_ord"
    "HOL-Library.List_Lenlexorder"
    "HOL-ex.Peano_Axioms"
begin

section \<open>Abstract Renaming\<close>

locale renaming_apart =
  fixes
    renaming :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes
    renaming_correct: "finite V \<Longrightarrow> renaming V x \<notin> V" and
    inj_renaming: "finite V \<Longrightarrow> inj (renaming V)"


subsection \<open>Interpretation to Prove That Assumptions Are Consistent\<close>


subsubsection \<open>Renaming Apart @{typ nat}\<close>

experiment begin

definition renaming_apart_nats where
  "renaming_apart_nats V = (let m = Max V in (\<lambda>x. Suc (x + m)))"

interpretation renaming_apart_nats: renaming_apart renaming_apart_nats
proof unfold_locales
  show "\<And>V x. finite V \<Longrightarrow> renaming_apart_nats V x \<notin> V"
    unfolding renaming_apart_nats_def Let_def by (meson Max.coboundedI Suc_le_lessD not_add_less2)
next
  show "\<And>V. inj (renaming_apart_nats V)"
    unfolding renaming_apart_nats_def Let_def by (rule injI) simp
qed

end

(* lemma (in peano) add_comm: "add m n = add n m"
  by (induct m) (simp_all add: add_zero_right add_succ_right)

lemma (in peano)
  assumes "finite X"
  shows "\<exists>y. \<forall>x. (add x y) \<notin> X"
  using assms(1)
proof (induction X rule: finite_induct)
  case empty
  then show ?case
    by simp
next
  case (insert x F)
  then obtain y where "\<forall>x. local.add x y \<notin> F"
    by auto
  then show ?case
    using insert.hyps
    apply -
    apply (rule exI[of _ "add (succ x) y"])
    unfolding add_assoc[of _ "succ x" y, symmetric]
    apply simp
    unfolding add_succ_right add_succ
    unfolding add_comm[of _ x]
    unfolding add_assoc
    find_theorems "card _ \<le> card _"
    find_theorems "bij_betw _ _ _ \<Longrightarrow> ?P (card _) (card _)"
    using Finite_Set.bij_betw_same_card[unfolded bij_betw_def]
    sorry
qed *)

(* lemma
  fixes X :: "nat set" and f :: "nat \<Rightarrow> nat"
  assumes "finite X"
  shows "\<exists>n :: nat. \<forall>x \<in> X. (f ^^ n) x \<notin> X"
  using assms
proof (rule contrapos_pp)
  assume "\<nexists>n. \<forall>x\<in>X. (f ^^ n) x \<notin> X"
  then show "infinite X" *)
(* 
lemma (in peano)
  assumes "finite X"
  shows "\<exists>n :: nat. \<forall>x \<in> X. (succ ^^ n) x \<notin> X"
  using assms(1)
proof (induction X rule: finite_induct)
  case empty
  then show ?case
    by simp
next
  case (insert x F)
  then obtain n where "\<forall>x\<in>F. (succ ^^ n) x \<notin> F"
    by auto
  then show ?case
    using insert.hyps
    sledgehammer
    sorry
qed
proof (rule contrapos_pp)
  assume "\<nexists>n. \<forall>x\<in>X. (succ ^^ n) x \<notin> X"
  then show "infinite X"
    apply simp
    sledgehammer
    using Suc_funpow finite_nat_set_iff_bounded not_add_less1
    by (metis ) *)

(* 
subsubsection \<open>Renaming Apart @{typ string}\<close>

experiment begin

term lenlex
typ string

term "max :: nat \<Rightarrow> _ \<Rightarrow> _"

lemma
  assumes "finite X" and "x \<in> X"
  shows "x \<le> Finite_Set.fold max y X"
  using assms
  apply (induction X arbitrary: x rule: finite_induct)
  apply simp
  apply simp
  apply auto

definition renaming_apart_strings :: "string set \<Rightarrow> string \<Rightarrow> string" where
  "renaming_apart_strings V = (let m = Finite_Set.fold max [] V in (\<lambda>x. x @ ''a'' @ m ))"


interpretation renaming_apart_nats: renaming_apart renaming_apart_strings
proof unfold_locales
  fix V x
  show "finite V \<Longrightarrow> renaming_apart_strings V x \<notin> V"
    unfolding renaming_apart_strings_def Let_def
    apply (induction V rule: finite_induct)
    apply simp
    sledgehammer
    apply simp
    
    by (meson Max.coboundedI Suc_le_lessD not_add_less2)
next
  show "\<And>V. inj (renaming_apart_strings V)"
    unfolding renaming_apart_strings_def Let_def
    by (rule injI) simp
qed

end *)

end