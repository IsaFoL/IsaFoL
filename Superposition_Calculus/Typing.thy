theory Typing
  imports Main
begin

locale typing =
  fixes is_typed is_welltyped
  assumes is_typed_if_is_welltyped: 
    "\<And>expr. is_welltyped expr \<Longrightarrow> is_typed expr"

(* TODO: Should not be a locale *)
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

(* TODO: Name *)
lemma typed_welltyped:
  assumes "typed expr \<tau>" "welltyped expr \<tau>'"
  shows "welltyped expr \<tau>"
  using assms typed_if_welltyped
  by blast

end

definition uniform_typed_lifting where 
  "uniform_typed_lifting to_set sub_typed expr \<equiv> \<exists>\<tau>. \<forall>sub \<in> to_set expr. sub_typed sub \<tau>"

definition is_typed_lifting where 
  "is_typed_lifting to_set sub_is_typed expr \<equiv> \<forall>sub \<in> to_set expr. sub_is_typed sub"

locale uniform_typing_lifting = 
  sub: explicit_typing where typed = sub_typed and welltyped = sub_welltyped
for sub_typed sub_welltyped :: "'sub \<Rightarrow> 'ty \<Rightarrow> bool" +
fixes to_set :: "'expr \<Rightarrow> 'sub set"
begin

abbreviation is_typed where
  "is_typed \<equiv> uniform_typed_lifting to_set sub_typed"

lemmas is_typed_def = uniform_typed_lifting_def[of to_set sub_typed]

abbreviation is_welltyped where
  "is_welltyped \<equiv> uniform_typed_lifting to_set sub_welltyped"
  
lemmas is_welltyped_def = uniform_typed_lifting_def[of to_set sub_welltyped]

sublocale typing where is_typed = is_typed and is_welltyped = is_welltyped
proof unfold_locales
  fix expr
  assume "is_welltyped expr"  
  then show "is_typed expr"
    using sub.typed_if_welltyped
    unfolding is_typed_def is_welltyped_def
    by auto
qed

end

locale typing_lifting =
  sub: typing where is_typed = sub_is_typed and is_welltyped = sub_is_welltyped
for sub_is_typed sub_is_welltyped :: "'sub \<Rightarrow> bool" +
fixes 
  to_set :: "'expr \<Rightarrow> 'sub set"
begin

abbreviation is_typed where
  "is_typed \<equiv> is_typed_lifting to_set sub_is_typed"

lemmas is_typed_def = is_typed_lifting_def[of to_set sub_is_typed]

abbreviation is_welltyped where
  "is_welltyped \<equiv> is_typed_lifting to_set sub_is_welltyped"

lemmas is_welltyped_def = is_typed_lifting_def[of to_set sub_is_welltyped]

sublocale typing where is_typed = is_typed and is_welltyped = is_welltyped
proof unfold_locales
  fix expr
  assume "is_welltyped expr"
  then show "is_typed expr"
    using sub.is_typed_if_is_welltyped
    unfolding is_typed_def is_welltyped_def
    by simp
qed

end

end
