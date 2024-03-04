theory Ground_Select
  imports
    Ground_Clause
begin

locale generic_select =
  fixes select :: "'a clause \<Rightarrow> 'a clause"
  assumes
    select_subset: "\<And>C. select C \<subseteq># C" and
    select_negative_lits: "\<And>C L. L \<in># select C \<Longrightarrow> is_neg L"

end