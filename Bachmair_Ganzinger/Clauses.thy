(*  Title:       Main and Side Clauses
    Author:      Anders Schlichtkrull, 2017
    Maintainer:  Anders Schlichtkrull
*)

theory Clauses imports "../lib/Clausal_Logic" begin

section {* Main and Side Clauses *}

subsection {* Main and side clauses *} (* Should maybe be in Clausal_Logic *)

definition "main_clause \<equiv> (\<lambda>(D,As). D + negs (mset As))"
abbreviation "side_clause \<equiv> (\<lambda>(C,As). C + poss As)"
definition "side_clauses Cs \<equiv> mset (map side_clause Cs)"

(* "'b" represents "'a multiset" and "'a list" *)
abbreviation get_C :: "'a clause * 'b \<Rightarrow> 'a clause" where 
  "get_C \<equiv> fst"

abbreviation get_As :: "'a clause * 'b \<Rightarrow> 'b" where 
  "get_As \<equiv> snd"
  
definition "Union_Cs CAs \<equiv> \<Union># (mset (map get_C CAs))"

lemma get_C_get_As_side_clauses:
 "CA \<in> set CAs \<Longrightarrow> (get_C CA) + poss (get_As CA) \<in># side_clauses CAs"
  unfolding side_clauses_def by auto

lemma get_C_Union_Cs[simp]: "x \<in> set CAs \<Longrightarrow> get_C x \<subseteq># Union_Cs CAs"
proof -
  assume "x \<in> set CAs"
  then have "get_C x \<in># (mset (map get_C CAs))" by auto
  then show "get_C x \<subseteq># Union_Cs CAs" unfolding Union_Cs_def
    by (simp add: sum_mset.remove)
qed

  

end