theory Multiset_Even_More
imports "../lib/Multiset_More"
begin

section \<open>Even More about Multisets\<close>

subsection \<open>Mutlisets and functions\<close>

theorem range_image_mset:
  assumes "\<forall>D. D \<in># Ds \<longrightarrow> D \<in> range f" 
  shows "Ds \<in> range (image_mset f)"
proof -
  have "\<forall>D. D \<in># Ds \<longrightarrow> (\<exists>C. f C = D)" using assms by blast
  then obtain f_i where f_p: "\<forall>D. D \<in># Ds \<longrightarrow> (f (f_i D) = D)" by metis
  define Cs where "Cs \<equiv> image_mset f_i Ds"
  from f_p Cs_def have "image_mset f Cs = Ds" by auto
  then show ?thesis by blast
qed

subsection \<open>Multisets and lists\<close>

definition list_of_multiset :: "'a multiset \<Rightarrow> 'a list" where
  "list_of_multiset m = (SOME l. m = mset l)"
  
lemma list_of_multiset_exi: "\<exists>l. m = mset l"
proof (induction rule: multiset_induct)
  case empty
  then show ?case by auto
next
  case (add x M)
  then obtain l where "M = mset l" by auto
  then have "add_mset x M = mset (x#l)" by auto
  then show ?case by blast
qed

lemma [simp]: "mset (list_of_multiset m) = m"
  by (metis (mono_tags, lifting) ex_mset list_of_multiset_def someI_ex)

theorem range_mset_map:
  assumes "\<forall>D. D \<in># Ds \<longrightarrow> D \<in> range f" 
  shows "Ds \<in> range (\<lambda>Cl. mset (map f Cl))"
proof -
  have "Ds \<in> range (image_mset f)" by (simp add: assms range_image_mset)
  then obtain Cs where Cs_p: "image_mset f Cs = Ds" by auto
  define Cl where "Cl = list_of_multiset Cs"
  then have "mset Cl = Cs" by auto
  then have "image_mset f (mset Cl) = Ds" using Cs_p by auto
  then have "mset (map f Cl) = Ds" by auto
  then show ?thesis by auto
qed
  
end