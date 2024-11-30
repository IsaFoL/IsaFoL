theory Typing
  imports Main
begin

locale typing =
  fixes is_typed is_welltyped
  assumes is_typed_if_is_welltyped: 
    "\<And>expr. is_welltyped expr \<Longrightarrow> is_typed expr"

locale predicate_typed = 
  fixes typed :: "'expr \<Rightarrow> 'ty \<Rightarrow> bool"
  assumes right_unique: "right_unique typed"
begin

abbreviation is_typed where
  "is_typed expr \<equiv> \<exists>\<tau>. typed expr \<tau>"

lemmas right_uniqueD [dest] = right_uniqueD[OF right_unique] 

end

locale explicit_typing =
  typed: predicate_typed where typed = typed +
  welltyped: predicate_typed where typed = welltyped
for typed welltyped :: "'expr \<Rightarrow> 'ty \<Rightarrow> bool" +
assumes typed_if_welltyped: "\<And>expr \<tau>. welltyped expr \<tau> \<Longrightarrow> typed expr \<tau>"
begin

abbreviation is_typed where
  "is_typed \<equiv> typed.is_typed"

abbreviation is_welltyped where
  "is_welltyped \<equiv> welltyped.is_typed"

sublocale typing where is_typed = is_typed and is_welltyped = is_welltyped
   using typed_if_welltyped
   by unfold_locales auto

end

(* TODO: *)
fun uniform_typed_lifting where 
  "uniform_typed_lifting to_set typed_sub expr \<longleftrightarrow> (\<exists>\<tau>. \<forall>sub \<in> to_set expr. typed_sub sub \<tau>)"

locale uniform_typing_lifting = 
  sub: explicit_typing where typed = typed_sub and welltyped = welltyped_sub
for typed_sub welltyped_sub :: "'sub \<Rightarrow> 'ty \<Rightarrow> bool" +
fixes to_set :: "'expr \<Rightarrow> 'sub set"
begin

abbreviation is_typed where
  "is_typed \<equiv> uniform_typed_lifting to_set typed_sub"

abbreviation is_welltyped where
  "is_welltyped \<equiv> uniform_typed_lifting to_set welltyped_sub"

sublocale typing where is_typed = is_typed and is_welltyped = is_welltyped
proof unfold_locales
  fix expr
  assume "is_welltyped expr"  
  then show "is_typed expr"
    using sub.typed_if_welltyped
    by auto
qed

end

(* TODO: *)
fun is_typed_lifting where 
  "is_typed_lifting to_set is_typed_sub expr \<longleftrightarrow> (\<forall>sub \<in> to_set expr. is_typed_sub sub)"

locale typing_lifting =
  sub: typing where is_typed = is_typed_sub and is_welltyped = is_welltyped_sub
for is_typed_sub is_welltyped_sub :: "'sub \<Rightarrow> bool" +
fixes 
  to_set :: "'expr \<Rightarrow> 'sub set"
begin

abbreviation is_typed where
  "is_typed \<equiv> is_typed_lifting to_set is_typed_sub"

abbreviation is_welltyped where
  "is_welltyped \<equiv> is_typed_lifting to_set is_welltyped_sub"

sublocale typing where is_typed = is_typed and is_welltyped = is_welltyped
proof unfold_locales
  fix expr
  assume "is_welltyped expr"
  then show "is_typed expr"
    using sub.is_typed_if_is_welltyped
    by simp
qed

end

end
