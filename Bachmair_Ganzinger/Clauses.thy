(*  Title:       Main and Side Clauses
    Author:      Anders Schlichtkrull, 2017
    Maintainer:  Anders Schlichtkrull
*)

theory Clauses imports "../lib/Clausal_Logic" begin

section {* Main and Side Clauses *}

subsection {* Main and side clauses *} (* Should maybe be in Clausal_Logic *)

definition "main_clause \<equiv> (\<lambda>(D,As). D + negs (mset As))"
abbreviation "side_clause \<equiv> (\<lambda>(C,As). C + poss As)"
definition "side_clauses Cs \<equiv> mset (map side_clause Cs)"

end