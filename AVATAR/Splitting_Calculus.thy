(*  Title:       Abstract Splitting Calculus
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2018
*)

section \<open>Abstract Splitting Calculus\<close>

theory Splitting_Calculus
  imports
    Splitting_Preliminaries
begin


subsection \<open>The Base Calculus\<close>

locale base_calculus = calculus Bot for Bot :: "'f set" +
  fixes
    lt_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes
    wf_lt_F: "wfP (\<prec>)" and
    Red_F_compact: "C \<in> Red_F N \<Longrightarrow> \<exists>N' \<subseteq> N. finite N' \<and> C \<in> Red_F N'"
begin

end


subsection \<open>The Splitting Calculus\<close>

datatype ('f, 'x) atom =
  Formula 'f
| Extra_Atom 'x

type_synonym ('f, 'x) component = "('f, 'x) atom literal"

type_synonym ('f, 'x) assertion = "('f, 'x) component set"

datatype ('f, 'x) aclause =
  AClause (fmla_of: 'f) (assert_of: "('f, 'x) assertion")

fun cls_of_acls :: "('f, 'x) aclause \<Rightarrow> ('f, 'x) atom clause" where
  "cls_of_acls (AClause C) A

type_synonym ('f, 'x) ainference = "('f, 'x) aclause inference"

locale splitting_calculus = base_calculus _ _ _ _ _ Bot for Bot :: "'f set" +
  fixes
    thy_U :: "'f set"
begin



end

end
