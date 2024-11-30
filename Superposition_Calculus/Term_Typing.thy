theory Term_Typing
  imports Typing Context_Extra
begin

type_synonym ('f, 'ty) fun_types = "'f \<Rightarrow> 'ty list \<times> 'ty" 

locale context_compatible_typing = 
  fixes Fun typed
  assumes 
   context_compatible [intro]:
    "\<And>t t' c \<tau> \<tau>'.
      typed t \<tau>' \<Longrightarrow>
      typed t' \<tau>' \<Longrightarrow>
      typed (Fun\<langle>c; t\<rangle>) \<tau> \<Longrightarrow>
      typed (Fun\<langle>c; t'\<rangle>) \<tau>"

locale subterm_typing = 
  fixes Fun typed
  assumes
    subterm': "\<And>f ts \<tau> . typed (Fun f ts) \<tau> \<Longrightarrow> \<forall>t\<in>set ts. \<exists>\<tau>'. typed t \<tau>'"
begin

lemma subterm: "typed (Fun\<langle>c; t\<rangle>) \<tau> \<Longrightarrow> \<exists>\<tau>. typed t \<tau>"
proof(induction c arbitrary: \<tau>)
  case Hole
  then show ?case
    by auto
next
  case (More f ss1 c ss2)

 then have "typed (Fun f (ss1 @ Fun\<langle>c;t\<rangle> # ss2)) \<tau>"
    by simp

  then have "\<exists>\<tau>. typed (Fun\<langle>c;t\<rangle>) \<tau>"
    using subterm'
    by simp

  then obtain \<tau>' where "typed (Fun\<langle>c;t\<rangle>) \<tau>'"
    by blast

  then show ?case 
    using More.IH
    by simp
qed

end

locale term_typing =
  explicit_typing + 
  typed: context_compatible_typing where typed = typed +
  welltyped: context_compatible_typing where typed = welltyped +
  welltyped: subterm_typing where typed = welltyped +
assumes all_terms_are_typed: "\<And>t. is_typed t"

end
