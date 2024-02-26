theory Ground_Select
  imports
    Ground_Clause
begin

locale ground_select =
  fixes select :: "'f atom clause \<Rightarrow> 'f atom clause"
  assumes
    select_subset: "\<And>C. select C \<subseteq># C" and
    select_negative_lits: "\<And>C L. L \<in># select C \<Longrightarrow> is_neg L"

end