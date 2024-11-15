theory Typing
  imports Main
begin

locale typing =
  fixes is_typed is_welltyped
  assumes is_typed_if_is_welltyped: 
    "\<And>expr. is_welltyped expr \<Longrightarrow> is_typed expr"

locale explicit_typing =
  fixes typed welltyped
  assumes 
    typed_right_unique: "right_unique typed" and
    welltyped_right_unique: "right_unique welltyped" and
    typed_if_welltyped: "\<And>expr \<tau>. welltyped expr \<tau> \<Longrightarrow> typed expr \<tau>"
begin

definition is_typed where
  "is_typed expr \<equiv> \<exists>\<tau>. typed expr \<tau>"

definition is_welltyped where
  "is_welltyped expr \<equiv> \<exists>\<tau>. welltyped expr \<tau>"

sublocale typing where is_typed = is_typed and is_welltyped = is_welltyped
   using typed_if_welltyped
   by unfold_locales (auto simp: is_typed_def is_welltyped_def)

lemmas typing_defs = is_typed_def is_welltyped_def

end

locale uniform_explicit_typing_lifting = 
  sub: explicit_typing where typed = typed_sub and welltyped = welltyped_sub
for typed_sub welltyped_sub :: "'sub \<Rightarrow> 'ty \<Rightarrow> bool" +
fixes 
  to_set :: "'expr \<Rightarrow> 'sub set" 
assumes
  to_set_not_empty: "\<And>expr. to_set expr \<noteq> {}" (* TODO: Better here or in definitions? *)
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
      using to_set_not_empty right_uniqueD[OF sub.typed_right_unique] 
      unfolding typed_def
      by blast
  qed
next
   show "right_unique welltyped"
  proof(rule right_uniqueI)
    fix expr \<tau> \<tau>'
    assume "welltyped expr \<tau>" "welltyped expr \<tau>'"
    
    then show "\<tau> = \<tau>'"
      using to_set_not_empty right_uniqueD[OF sub.welltyped_right_unique] 
      unfolding welltyped_def
      by blast
  qed
next
  fix expr \<tau>
  assume "welltyped expr \<tau>"  
  then show "typed expr \<tau>"
    using sub.typed_if_welltyped
    unfolding welltyped_def typed_def
    by simp
qed

lemmas typing_defs = typed_def welltyped_def is_typed_def is_welltyped_def

end

locale typing_lifting =
  sub: typing where is_typed = is_typed_sub and is_welltyped = is_welltyped_sub
for is_typed_sub is_welltyped_sub :: "'sub \<Rightarrow> bool" +
fixes 
  to_set :: "'expr \<Rightarrow> 'sub set"
begin

definition is_typed where
  "is_typed expr \<equiv> \<forall>sub \<in> to_set expr. is_typed_sub sub"

definition is_welltyped where
  "is_welltyped expr \<equiv> \<forall>sub \<in> to_set expr. is_welltyped_sub sub"

sublocale typing where is_typed = is_typed and is_welltyped = is_welltyped
proof unfold_locales
  fix expr
  assume "is_welltyped expr"
  then show "is_typed expr"
    unfolding is_typed_def is_welltyped_def
    using sub.is_typed_if_is_welltyped
    by blast
qed

lemmas typing_defs = is_typed_def is_welltyped_def

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
