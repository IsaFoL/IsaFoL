theory Multiset_Extra
  imports "HOL-Library.Multiset"
begin
  
definition is_maximal_wrt where
  "is_maximal_wrt R x M \<longleftrightarrow> (\<forall>y \<in># M - {#x#}. \<not> (R x y))"

end