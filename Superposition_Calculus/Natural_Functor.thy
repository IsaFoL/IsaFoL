theory Natural_Functor
  imports Main
begin

locale natural_functor =
  fixes
    map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b" and
    to_set :: "'b \<Rightarrow> 'a set"
  assumes
    map_comp: "\<And>b f g. map (f \<circ> g) b = map f (map g b)" and
    map_id: "\<And>b. map id b = b" and
    map_cong: "\<And>b f g. (\<And>a. a \<in> to_set b \<Longrightarrow> f a = g a) \<Longrightarrow> map f b = map g b" and
    to_set_map: "\<And>b f. to_set (map f b) = f ` to_set b" and
    exists_functor: "\<And>a. \<exists>b. a \<in> to_set b"

locale natural_functor_conversion =
  natural_functor +
  fixes
    map_to :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd" and
    map_from :: "('b \<Rightarrow> 'a) \<Rightarrow> 'd \<Rightarrow> 'c" and
    map' :: "('b \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'd" and
    to_set' :: "'d \<Rightarrow> 'b set"
  assumes
    to_set_map_from: "\<And>f d. to_set (map_from f d) = f ` to_set' d" and
    conversion_map_comp: "\<And>c f g. map (f \<circ> g) c = map_from f (map_to g c)" and
    map'_comp: "\<And>d f g. map' (f \<circ> g) d = map_to f (map_from g d)" and
    map'_id: "\<And>d. map' id d = d"

end
