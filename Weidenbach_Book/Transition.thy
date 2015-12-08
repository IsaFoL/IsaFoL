theory Transition
imports Main

begin
section \<open>Transition\<close>
text \<open>We define here properties to define properties after all possible transitions.\<close>
abbreviation "no_step step S \<equiv> (\<forall>S'. \<not>step S S')"

definition full :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_\<^sup>+\<^sup>\<down>") where
"full transf = (\<lambda>S S'. tranclp transf S S' \<and> (\<forall>S''. \<not> transf S' S''))"

definition full0:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_\<^sup>\<down>") where
"full0 transf = (\<lambda>S S'. rtranclp transf S S' \<and> (\<forall>S''. \<not> transf S' S''))"

lemma rtranclp_fullI:
  "R\<^sup>*\<^sup>* a b \<Longrightarrow> full R b c \<Longrightarrow> full R a c"
  unfolding full_def by auto

lemma tranclp_fullI:
  "R\<^sup>+\<^sup>+ a b \<Longrightarrow> full R b c \<Longrightarrow> full R a c"
  unfolding full_def by auto

lemma rtranclp_full0I:
  "R\<^sup>*\<^sup>* a b \<Longrightarrow> full0 R b c \<Longrightarrow> full0 R a c"
  unfolding full0_def by auto
lemma tranclp_full0_fullI:
  "R\<^sup>+\<^sup>+ a b \<Longrightarrow> full0 R b c \<Longrightarrow> full R a c"
  unfolding full0_def full_def by auto

lemma full0_unfold:
  "full0 r S S' \<longleftrightarrow> ((S = S' \<and> no_step r S') \<or> full r S S')"
  unfolding full0_def full_def by (auto simp add: Nitpick.rtranclp_unfold)

lemma wf_exists_normal_form:
  assumes wf:"wf {(x, y). R y x}"
  shows "\<exists>b. R\<^sup>*\<^sup>* a b \<and> no_step R b"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence H: "\<And>b. \<not> R\<^sup>*\<^sup>* a b \<or> \<not>no_step R b"
    by blast
  def F \<equiv> "rec_nat a (\<lambda>i b. SOME c. R b c)"
  have [simp]: "F 0 = a"
    unfolding F_def by auto
  have [simp]: "\<And>i. F (Suc i) = (SOME b. R (F i) b)"
    using F_def by simp
  { fix i
    have "\<forall>j<i. R (F j) (F (Suc j))"
      proof (induction i)
        case 0
        thus ?case by auto
      next
        case (Suc i)
        hence "R\<^sup>*\<^sup>* a (F i)"
          by (induction i) auto
        hence "R (F i) (SOME b. R (F i) b)"
          using H by (simp add: someI_ex)
        hence "\<forall>j < Suc i. R (F j) (F (Suc j))"
          using H Suc by (simp add: less_Suc_eq)
        thus ?case by fast
      qed
  }
  hence "\<forall>j. R (F j) (F (Suc j))" by blast
  thus False
    using wf unfolding wfP_def wf_iff_no_infinite_down_chain by blast
qed

lemma wf_exists_normal_form_full0:
  assumes wf:"wf {(x, y). R y x}"
  shows "\<exists>b. full0 R a b"
  using wf_exists_normal_form[OF assms] unfolding full0_def by blast

end