theory Typing
  imports Main
begin

locale typing =
  fixes is_typed is_welltyped
  assumes is_typed_if_is_welltyped: 
    "\<And>expr. is_welltyped expr \<Longrightarrow> is_typed expr"

(* TODO Name *)
locale dep_typing =
  fixes is_typed is_welltyped
  assumes is_typed_if_is_welltyped: 
    "\<And>\<T> expr. is_welltyped \<T> expr \<Longrightarrow> is_typed \<T> expr"
begin

sublocale typing where is_typed = "is_typed \<T>" and is_welltyped = "is_welltyped \<T>"
  using is_typed_if_is_welltyped
  by unfold_locales

end

locale explicit_typing =
  fixes typed welltyped
  assumes 
    typed_right_unique: "right_unique typed" and
    welltyped_right_unique: "right_unique welltyped" and
    typed_if_welltyped: "\<And>expr \<tau>. welltyped expr \<tau> \<Longrightarrow> typed expr \<tau>"
begin

abbreviation is_typed where
  "is_typed expr \<equiv> \<exists>\<tau>. typed expr \<tau>"

abbreviation is_welltyped where
  "is_welltyped expr \<equiv> \<exists>\<tau>. welltyped expr \<tau>"

sublocale typing where is_typed = is_typed and is_welltyped = is_welltyped
   using typed_if_welltyped
   by unfold_locales auto

lemmas right_uniqueD [dest] = 
  right_uniqueD[OF typed_right_unique] 
  right_uniqueD[OF welltyped_right_unique]

end

locale dep_explicit_typing =
  fixes typed welltyped
  assumes 
    typed_right_unique: "\<And>\<T>. right_unique (typed \<T>)" and
    welltyped_right_unique: "\<And>\<T>. right_unique (welltyped \<T>)" and
    typed_if_welltyped: "\<And>\<T> expr \<tau>. welltyped \<T> expr \<tau> \<Longrightarrow> typed \<T> expr \<tau>"
begin

sublocale explicit_typing where typed = "typed \<T>" and welltyped = "welltyped \<T>"
  by unfold_locales (rule typed_if_welltyped typed_right_unique welltyped_right_unique)+

sublocale dep_typing where is_typed = is_typed and is_welltyped = is_welltyped
  using is_typed_if_is_welltyped
  by unfold_locales

end

locale uniform_explicit_typing_lifting = 
  sub: explicit_typing where typed = typed_sub and welltyped = welltyped_sub
for typed_sub welltyped_sub :: "'sub \<Rightarrow> 'ty \<Rightarrow> bool" +
fixes 
  to_set :: "'expr \<Rightarrow> 'sub set" 
assumes
  to_set_not_empty: "\<And>expr. to_set expr \<noteq> {}"
begin

definition typed where
  "typed expr \<tau> \<equiv> \<forall>sub \<in> to_set expr. typed_sub sub \<tau>"

definition welltyped where
  "welltyped expr \<tau> \<equiv> \<forall>sub \<in> to_set expr. welltyped_sub sub \<tau>"

sublocale explicit_typing where typed = typed and welltyped = welltyped
proof unfold_locales
  show "right_unique typed"
  proof(rule right_uniqueI)
    fix expr \<tau> \<tau>'
    assume "typed expr \<tau>" "typed expr \<tau>'"
    
    then show "\<tau> = \<tau>'"
      unfolding typed_def
      using to_set_not_empty right_uniqueD[OF sub.typed_right_unique] 
      by blast
  qed
next
  show "right_unique welltyped"
  proof(rule right_uniqueI)
    fix expr \<tau> \<tau>'
    assume "welltyped expr \<tau>" "welltyped expr \<tau>'"
    
    then show "\<tau> = \<tau>'"
      unfolding welltyped_def
      using to_set_not_empty right_uniqueD[OF sub.welltyped_right_unique] 
      by blast
  qed
next
  fix expr \<tau>
  assume "welltyped expr \<tau>"  
  then show "typed expr \<tau>"
    unfolding welltyped_def typed_def
    using sub.typed_if_welltyped
    by simp
qed

end

locale typing_lifting =
  sub: typing where is_typed = is_typed_sub and is_welltyped = is_welltyped_sub
for is_typed_sub is_welltyped_sub :: "'sub \<Rightarrow> bool" +
fixes 
  to_set :: "'expr \<Rightarrow> 'sub set"
begin

abbreviation is_typed where
  "is_typed expr \<equiv> \<forall>sub \<in> to_set expr. is_typed_sub sub"

abbreviation is_welltyped where
  "is_welltyped expr \<equiv> \<forall>sub \<in> to_set expr. is_welltyped_sub sub"

sublocale typing where is_typed = is_typed and is_welltyped = is_welltyped
proof unfold_locales
  fix expr
  assume "is_welltyped expr"
  then show "is_typed expr"
    using sub.is_typed_if_is_welltyped
    by blast
qed

end

subsection\<open>Unified naming\<close> (* TODO ? *)

locale typed_def =
  fixes typed_def welltyped_def :: "'expr \<Rightarrow> 'ty \<Rightarrow> bool" 
begin 

abbreviation typed where "typed \<equiv> typed_def"
abbreviation welltyped where "welltyped \<equiv> welltyped_def"

end

locale is_typed_def =
  fixes is_typed_def is_welltyped_def :: "'expr \<Rightarrow> bool" 
begin 

abbreviation is_typed where "is_typed \<equiv> is_typed_def"
abbreviation is_welltyped where "is_welltyped \<equiv> is_welltyped_def"

end

end
