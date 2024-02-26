theory Ground_Clause
  imports
    Regular_Tree_Relations.Ground_Terms
    Saturation_Framework_Extensions.Clausal_Calculus

    Uprod_Extra
begin

abbreviation Pos_Upair (infix "\<approx>" 66) where
  "Pos_Upair x y \<equiv> Pos (Upair x y)"

abbreviation Neg_Upair (infix "!\<approx>" 66) where
  "Neg_Upair x y \<equiv> Neg (Upair x y)"

type_synonym 'f atom = "'f gterm uprod"

end