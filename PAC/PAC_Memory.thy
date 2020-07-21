theory PAC_Memory
  imports PAC_Polynomials
begin

section \<open>Abstract Specification\<close>

datatype mset_state =
  MSET_State (get_polys: \<open>nat \<Rightarrow> mset_polynom option\<close>)


section \<open>Intermediate Version\<close>
end