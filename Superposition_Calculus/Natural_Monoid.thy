theory Natural_Monoid
  imports Main
begin

locale natural_monoid = 
  fixes 
    to_set :: "'expr \<Rightarrow> 'sub set" and
    plus :: "'expr \<Rightarrow> 'expr \<Rightarrow> 'expr" and
    wrap :: "'sub \<Rightarrow> 'expr" (* TODO: Not typical for Monoid *)
  assumes
    to_set_plus: "\<And>expr expr'. to_set (plus expr expr') = (to_set expr) \<union> (to_set expr')" and
    to_set_wrap: "\<And>sub. to_set (wrap sub) = {sub}"
begin

abbreviation add where 
  "add sub expr \<equiv> plus (wrap sub) expr" 

lemma to_set_add: "\<And>sub expr. to_set (add sub expr) = insert sub (to_set expr)"
  using to_set_plus to_set_wrap
  by simp  

end

end
