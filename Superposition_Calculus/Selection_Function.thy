theory Selection_Function
  imports
    Ground_Clause
begin

locale select =
  fixes sel :: "'a clause \<Rightarrow> 'a clause"
  assumes
    select_subset: "\<And>C. sel C \<subseteq># C" and
    select_negative_lits: "\<And>C L. L \<in># sel C \<Longrightarrow> is_neg L"

end
