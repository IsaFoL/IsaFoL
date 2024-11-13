theory Term_Order_Notation
  imports Main
begin

locale term_order_notation = 
  fixes less\<^sub>t :: "'t \<Rightarrow> 't \<Rightarrow> bool"
begin

notation less\<^sub>t (infix "\<prec>\<^sub>t" 50)

abbreviation "less_eq\<^sub>t \<equiv> (\<prec>\<^sub>t)\<^sup>=\<^sup>="

notation less_eq\<^sub>t (infix "\<preceq>\<^sub>t" 50)

end
  
end
