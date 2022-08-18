theory Given_Clause_Loops_Util
  imports "HOL-Library.Multiset"
begin

lemma singletons_in_mult1: "(x, y) \<in> R \<Longrightarrow> ({#x#}, {#y#}) \<in> mult1 R"
  by (metis add_mset_add_single insert_DiffM mult1I single_eq_add_mset)

lemma singletons_in_mult: "(x, y) \<in> R \<Longrightarrow> ({#x#}, {#y#}) \<in> mult R"
  by (simp add: mult_def singletons_in_mult1 trancl.intros(1))

end
