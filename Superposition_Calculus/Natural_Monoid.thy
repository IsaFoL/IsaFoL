theory Natural_Monoid
  imports Main
begin

locale natural_monoid = 
  fixes 
    to_set :: "'b \<Rightarrow> 'a set" and
    plus :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" and
    wrap :: "'a \<Rightarrow> 'b" (* TODO: Not typical for Monoid *)
  assumes
    to_set_plus: "\<And>b b'. to_set (plus b b') = (to_set b) \<union> (to_set b')" and
    to_set_wrap: "\<And>a. to_set (wrap a) = {a}"
begin

abbreviation add where 
  "add a b \<equiv> plus (wrap a) b" 

lemma to_set_add: "\<And>a b. to_set (add a b) = insert a (to_set b)"
  using to_set_plus to_set_wrap
  by simp  

end

end
