(*  Title:       Abstract Splitting Calculus
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2018
*)

section \<open>Abstract Splitting Calculus\<close>

theory Splitting_Calculus
  imports
    Splitting_Preliminaries
begin

datatype ('f, 'x) sym =
  Base_Sym 'f
| Extra_Sym 'x

type_synonym ('f, 'x) component = "('f, 'x) sym literal"

type_synonym ('f, 'x) assertion = "('f, 'x) component set"

datatype ('f, 'x) aclause =
  AClause (fmla_of: 'f) (assert_of: "('f, 'x) assertion")

type_synonym ('f, 'x) ainference = "('f, 'x) aclause inference"

locale base_calculus = compact_calculus _ _ _ _ _ Bot for Bot :: "'f set"
begin

end

locale splitting_calculus = base_calculus _ _ _ _ _ Bot for Bot :: "'f set"
begin

end

end
