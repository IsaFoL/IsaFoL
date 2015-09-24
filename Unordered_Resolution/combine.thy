definition combine :: "var_sym set \<Rightarrow> substitution \<Rightarrow> substitution \<Rightarrow> substitution" where
  "combine vars\<sigma>1 \<sigma>1 \<sigma>2 x = (if x \<in> vars\<sigma>1 then \<sigma>1 x else \<sigma>2 x)"

lemma combine1: "x \<in> vars\<sigma>1 \<Longrightarrow> combine vars\<sigma>1 \<sigma>1 \<sigma>2 x = \<sigma>1 x"
  unfolding combine_def by auto

lemma combine2: "x \<notin> vars\<sigma>1 \<Longrightarrow> combine vars\<sigma>1 \<sigma>1 \<sigma>2 x = \<sigma>2 x"
  unfolding combine_def by auto

lemma combinet1: 
  "varst t \<subseteq> vars\<sigma>1 \<Longrightarrow> t {combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>t = t {\<sigma>1}\<^sub>t"
  "varsts ts \<subseteq> vars\<sigma>1 \<Longrightarrow> ts {combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>t\<^sub>s = ts {\<sigma>1}\<^sub>t\<^sub>s"
apply (induction t and ts rule: sub.induct subs.induct)
apply (auto simp add: combine1)
done

lemma combinet2: 
  "varst t \<inter> vars\<sigma>1 = {} \<Longrightarrow> t {combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>t = t {\<sigma>2}\<^sub>t"
  "varsts ts \<inter> vars\<sigma>1 = {} \<Longrightarrow> ts {combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>t\<^sub>s = ts {\<sigma>2}\<^sub>t\<^sub>s"
apply (induction t and ts rule: sub.induct subs.induct)
using combine2 apply auto 
done

lemma combinel1: "varsl l \<subseteq> vars\<sigma>1 \<Longrightarrow> l {combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>l = l {\<sigma>1}\<^sub>l"
using combinet1 unfolding varsl_def by (cases l) auto

lemma combinel2: "varsl l \<inter> vars\<sigma>1 = {} \<Longrightarrow> l {combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>l = l {\<sigma>2}\<^sub>l"
using combinet2 unfolding varsl_def by (cases l) auto

lemma combinec1:
  assumes asm: "varsc c \<subseteq> vars\<sigma>1"
  shows "c {combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>l\<^sub>s = c {\<sigma>1}\<^sub>l\<^sub>s"
proof -
  {
    fix lcom
    assume "lcom \<in> c{combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>l\<^sub>s"
    then obtain l where l_p: "l \<in> c \<and> l {combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>l = lcom" by auto
    moreover
    then have "varsl l \<subseteq> vars\<sigma>1" using asm unfolding varsc_def by auto
    ultimately
    have "lcom = l {\<sigma>1}\<^sub>l" using combinel1 by auto
    then have "lcom \<in> c{\<sigma>1}\<^sub>l\<^sub>s" using l_p by auto
  }
  moreover
  {
    fix l\<sigma>1
    assume "l\<sigma>1 \<in> c {\<sigma>1}\<^sub>l\<^sub>s"
    then obtain l where l_p: "l \<in> c \<and> l {\<sigma>1}\<^sub>l = l\<sigma>1" by auto
    moreover
    then have "varsl l \<subseteq> vars\<sigma>1" using asm unfolding varsc_def by auto
    ultimately
    have "l\<sigma>1 = l {combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>l" using combinel1 by auto
    then have "l\<sigma>1 \<in> c{combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>l\<^sub>s" using l_p by auto
  }
  ultimately show ?thesis by auto
qed

lemma combinec2:
  assumes asm: "varsc c \<inter> vars\<sigma>1 = {}"
  shows "c {combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>l\<^sub>s = c {\<sigma>2}\<^sub>l\<^sub>s"
proof -
  {
    fix lcom
    assume "lcom \<in> c{combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>l\<^sub>s"
    then obtain l where l_p: "l \<in> c \<and> l {combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>l = lcom" by auto
    moreover
    then have "varsl l \<inter> vars\<sigma>1 = {}" using asm unfolding varsc_def by auto
    ultimately
    have "lcom = l {\<sigma>2}\<^sub>l" using combinel2 by auto
    then have "lcom \<in> c{\<sigma>2}\<^sub>l\<^sub>s" using l_p by auto
  } 
  moreover
  {
    fix l\<sigma>2
    assume "l\<sigma>2 \<in> c {\<sigma>2}\<^sub>l\<^sub>s"
    then obtain l where l_p: "l \<in> c \<and> l {\<sigma>2}\<^sub>l = l\<sigma>2" by auto
    moreover
    then have "varsl l \<inter> vars\<sigma>1 = {}" using asm unfolding varsc_def by auto
    ultimately
    have "l\<sigma>2 = l {combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>l" using combinel2 by auto
    then have "l\<sigma>2 \<in> c{combine vars\<sigma>1 \<sigma>1 \<sigma>2}\<^sub>l\<^sub>s" using l_p by auto
  }
  ultimately show ?thesis by auto
qed
