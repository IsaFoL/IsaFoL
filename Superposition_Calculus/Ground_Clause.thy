theory Ground_Clause
  imports
    Saturation_Framework_Extensions.Clausal_Calculus

    Ground_Term_Extra
    Ground_Ctxt_Extra
    Uprod_Extra
begin

abbreviation Pos_Upair (infix "\<approx>" 66) where
  "Pos_Upair x y \<equiv> Pos (Upair x y)"

abbreviation Neg_Upair (infix "!\<approx>" 66) where
  "Neg_Upair x y \<equiv> Neg (Upair x y)"

type_synonym 'f gatom = "'f gterm uprod"

no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
no_notation subst_apply_term (infixl "\<cdot>" 67)



end