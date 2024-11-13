theory Ground_Term_Extra
  imports "Regular_Tree_Relations.Ground_Terms"
begin

lemma gterm_is_fun: "is_Fun (term_of_gterm t)"
  by(cases t) simp

no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
no_notation subst_apply_term (infixl "\<cdot>" 67)

end
