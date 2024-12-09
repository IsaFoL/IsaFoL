theory Natural_Magma_Functor
  imports Natural_Magma Natural_Functor
begin

locale natural_magma_functor = natural_magma + natural_functor +
  assumes 
    map_wrap: "\<And>f a. map f (wrap a) = wrap (f a)" and 
    map_plus: "\<And>f b b'. map f (plus b b') = plus (map f b) (map f b')" 
begin

lemma map_add: "\<And>f a b. map f (add a b) = add (f a) (map f b)"
  unfolding add_def
  using map_plus map_wrap
  by simp

end

end
