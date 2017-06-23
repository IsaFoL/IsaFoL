(*  Title:       Multiset Even More
    Author:      Anders Schlichtkrull, 2017
    Maintainer:  Anders Schlichtkrull
*)

theory Multiset_Even_More
imports "$AFP/Nested_Multisets_Ordinals/Multiset_More"
begin

section \<open>Even More about Multisets\<close>
  
subsection \<open>Multisets and functions\<close>
  
theorem range_image_mset:
  assumes "set_mset Ds \<subseteq> range f" 
  shows "Ds \<in> range (image_mset f)"
proof -
  have "\<forall>D. D \<in># Ds \<longrightarrow> (\<exists>C. f C = D)" using assms by blast
  then obtain f_i where f_p: "\<forall>D. D \<in># Ds \<longrightarrow> (f (f_i D) = D)" by metis
  define Cs where "Cs \<equiv> image_mset f_i Ds"
  from f_p Cs_def have "image_mset f Cs = Ds" by auto
  then show ?thesis by blast
qed
  
subsection \<open>Multisets and lists\<close>

definition list_of_mset :: "'a multiset \<Rightarrow> 'a list" where
  "list_of_mset m = (SOME l. m = mset l)"
  
lemma list_of_mset_exi: "\<exists>l. m = mset l"
  using ex_mset by metis

lemma [simp]: "mset (list_of_mset m) = m"
  by (metis (mono_tags, lifting) ex_mset list_of_mset_def someI_ex)  

theorem range_mset_map:
  assumes "set_mset Ds \<subseteq> range f" 
  shows "Ds \<in> range (\<lambda>Cl. mset (map f Cl))"
proof -
  have "Ds \<in> range (image_mset f)" by (simp add: assms range_image_mset)
  then obtain Cs where Cs_p: "image_mset f Cs = Ds" by auto
  define Cl where "Cl = list_of_mset Cs"
  then have "mset Cl = Cs" by auto
  then have "image_mset f (mset Cl) = Ds" using Cs_p by auto
  then have "mset (map f Cl) = Ds" by auto
  then show ?thesis by auto
qed

theorem list_of_mset_empty[simp]:
  assumes "list_of_mset m = []"
  shows "m = {#}"
by (metis (full_types) assms ex_mset list_of_mset_def mset_zero_iff_right someI_ex) 
  

theorem in_mset_conv_nth: "(x \<in># mset xs) = (\<exists>i<length xs. xs ! i = x)"
  by (auto simp: in_set_conv_nth)
    
theorem in_mset_sum_list:
  assumes "L \<in># LL"
  assumes "LL \<in> set Ci"
  shows "L \<in># sum_list Ci"
  using assms by (induction Ci) auto
    
theorem in_mset_sum_list2:
  assumes "L \<in># sum_list Ci"
  obtains LL where
    "LL \<in> set Ci"
    "L \<in># LL"
  using assms by (induction Ci) auto
    
lemma subseteq_list_Union_mset:
  assumes "length Ci = n"
  assumes "length CAi = n"
  assumes "\<forall>i<n.  Ci ! i \<subseteq># CAi ! i "
  shows "\<Union>#mset Ci \<subseteq># \<Union>#mset CAi"
  using assms proof (induction n arbitrary: Ci CAi)
  case 0
  then show ?case by auto
next
  case (Suc n)
  from Suc have "\<forall>i<n. tl Ci ! i \<subseteq># tl CAi ! i"
    by (simp add: nth_tl) 
  hence "\<Union>#mset (tl Ci) \<subseteq># \<Union>#mset (tl CAi)" using Suc by auto
  moreover
  have "hd Ci \<subseteq># hd CAi" using Suc
    by (metis hd_conv_nth length_greater_0_conv zero_less_Suc)
  ultimately
  show "\<Union>#mset Ci \<subseteq># \<Union>#mset CAi"
    using Suc by (cases Ci; cases CAi) (auto intro: subset_mset.add_mono)
qed    
    
subsection \<open>More on multisets and functions\<close>

lemma image_mset_of_subset_list:
  assumes "image_mset \<eta> C' = mset lC"
  shows "\<exists>qC'. map \<eta> qC' = lC \<and> mset qC' = C'"
  using assms apply (induction lC arbitrary: C')
  subgoal by simp
  subgoal by (fastforce dest!: msed_map_invR intro: exI[of _ \<open>_ # _\<close>])
  done
  
lemma image_mset_of_subset: 
  assumes "A \<subseteq># image_mset \<eta> C'"
  shows "\<exists>A'. image_mset \<eta> A' = A \<and> A' \<subseteq># C'"
proof -
  define C where "C = image_mset \<eta> C'"
  
  define lA where "lA = list_of_mset A"
  define lD where "lD = list_of_mset (C-A)"
  define lC where "lC = lA @ lD"
    
  have "mset lC = C"
    using C_def assms unfolding lD_def lC_def lA_def by auto
  then have "\<exists>qC'. map \<eta> qC' = lC \<and> mset qC' = C'"
    using assms image_mset_of_subset_list unfolding C_def by metis
  then obtain qC' where qC'_p: "map \<eta> qC' = lC \<and> mset qC' = C'"
    by auto
  let ?lA' = "take (length lA) qC'"
  have m: "map \<eta> ?lA' = lA"
    using qC'_p lC_def
    by (metis append_eq_conv_conj take_map)
  let ?A' = "mset ?lA'"    
  
  have "image_mset \<eta> ?A' = A"
    using m using lA_def
    by (metis (full_types) ex_mset list_of_mset_def mset_map someI_ex)
  moreover
  have "?A' \<subseteq># C'"  
    using qC'_p unfolding lA_def
    using mset_take_subseteq by blast
  ultimately show ?thesis by blast
qed
    
(* Not actually about multisets... *)    
theorem "\<forall>i < length xs. P (xs ! i) \<Longrightarrow> \<forall>x \<in> set xs. P x"
  using in_mset_conv_nth[of _ xs] by auto
    
    
    
    
end