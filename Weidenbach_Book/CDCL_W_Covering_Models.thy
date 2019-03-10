theory CDCL_W_Covering_Models
  imports CDCL_W_Optimal_Model
begin

section \<open>Covering Models\<close>

locale covering_models =
  fixes
    \<rho> :: \<open>'v \<Rightarrow> bool\<close>
begin
text \<open>
  The first version of the calculus was obviously wrong, because there is no totality
  condition in the rule ConflCM.\<close>

definition model_is_dominating :: \<open>'v literal multiset \<Rightarrow> 'v literal multiset \<Rightarrow> bool\<close> where
\<open>model_is_dominating M M' \<longleftrightarrow>
  filter_mset (\<lambda>L. is_pos L \<and> \<rho> (atm_of L)) M \<subseteq># filter_mset (\<lambda>L. is_pos L \<and> \<rho> (atm_of L)) M'\<close>

end

end
