theory Term_Typing
  imports Typing Context_Extra
begin

type_synonym ('f, 'ty) fun_types = "'f \<Rightarrow> 'ty list \<times> 'ty" 
type_synonym ('v, 'ty) var_types = "'v \<Rightarrow> 'ty"

locale context_compatible_typing = explicit_typing +
  fixes Fun
  assumes 
    welltyped_context_compatible [intro]: 
    "\<And>t t' c \<tau> \<tau>'.
      welltyped t \<tau>' \<Longrightarrow>
      welltyped t' \<tau>' \<Longrightarrow>
      welltyped (Fun\<langle>c; t\<rangle>) \<tau> \<Longrightarrow>
      welltyped (Fun\<langle>c; t'\<rangle>) \<tau>" and
    typed_context_compatible: 
    "\<And>t t' c \<tau> \<tau>'.
      typed t \<tau>' \<Longrightarrow>
      typed t' \<tau>' \<Longrightarrow>
      typed (Fun\<langle>c; t\<rangle>) \<tau> \<Longrightarrow>
      typed (Fun\<langle>c; t'\<rangle>) \<tau>"

locale term_typing = 
  explicit_typing + context_compatible_typing

end
