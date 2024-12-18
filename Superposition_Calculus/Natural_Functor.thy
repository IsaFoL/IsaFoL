theory Natural_Functor
  imports Main
begin

(* TODO: Integration with built-in functor command possible? *)

locale natural_functor =
  fixes
    map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b" and
    to_set :: "'b \<Rightarrow> 'a set"
  assumes
    map_comp [simp]: "\<And>b f g. map f (map g b) = map (\<lambda>x. f (g x)) b" and
    map_ident [simp]: "\<And>b. map (\<lambda>x. x) b = b" and
    map_cong [cong]: "\<And>b f g. (\<And>a. a \<in> to_set b \<Longrightarrow> f a = g a) \<Longrightarrow> map f b = map g b" and
    to_set_map [simp]: "\<And>b f. to_set (map f b) = f ` to_set b" and
    exists_functor [intro]: "\<And>a. \<exists>b. a \<in> to_set b"
begin

lemma map_id [simp]: "map id b = b"
  unfolding id_def
  by(rule map_ident)

end

locale finite_natural_functor = natural_functor +
  assumes finite_to_set [intro]: "\<And>b. finite (to_set b)"

locale natural_functor_conversion =
  natural_functor +
  functor': natural_functor where map = map' and to_set = to_set'
  for map' :: "('b \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'd" and to_set' :: "'d \<Rightarrow> 'b set" +
  fixes
    map_to :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd" and
    map_from :: "('b \<Rightarrow> 'a) \<Rightarrow> 'd \<Rightarrow> 'c"
  assumes
    to_set_map_from [simp]: "\<And>f d. to_set (map_from f d) = f ` to_set' d" and
    to_set_map_to [simp]: "\<And>f c. to_set' (map_to f c) = f ` to_set c" and
    conversion_map_comp [simp]: "\<And>c f g. map_from f (map_to g c) = map (\<lambda>x. f (g x)) c" and
    conversion_map_comp' [simp]: "\<And>d f g. map_to f (map_from g d) = map' (\<lambda>x. f (g x)) d"

end
