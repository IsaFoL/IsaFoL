(*  Title: Implementation of CDCL with Two Watched Literals
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

section \<open>Implementation for 2 Watched-Literals\<close>

theory CDCL_Two_Watched_Literals_Implementation
imports CDCL_Two_Watched_Literals_Invariant
begin

datatype 'v twl_state_cands =
  TWL_State_Cand (twl_state: "'v twl_state")
    (propa_cand: "('v literal \<times> 'v twl_clause) list")
    (confl_cand: "'v twl_clause literal")

text \<open>While updating the clauses, there are several cases:
  \<^item> @{term L} is not watched and there is nothing to do;
  \<^item> there is a literal to be watched: there are swapped;
  \<^item> there is no literal to be watched, the other literal is not assigned: the clause
  is a propagate candidate;
  \<^item> there is no literal to be watched, but the other literal is true: there is nothing to
  do;
  \<^item> there is no literal to be watched, but the other literal is false: the clause is a
  conflict candidate.\<close>
definition
  rewatch_nat_cand ::
  "'v literal \<Rightarrow> 'v twl_state \<Rightarrow> 'v twl_clause \<Rightarrow>
     'v twl_clause \<times> ('v literal \<times> 'v twl_clause) option \<times> 'v twl_clause option"
where
  "rewatch_nat_cand L S C =
   (if - L \<in> set (watched C) then
      case filter (\<lambda>L'. L' \<notin> set (watched C) \<and> - L' \<notin> insert L (lits_of_l (trail S)))
         (unwatched C) of
        [] \<Rightarrow> (if trail S \<Turnstile>as CNot (mset (remove1 L (watched C)))
          then (C, None, Some C)
          else if set (remove1 L (watched C)) \<subseteq> set (map lit_of (trail S))
            then (C, None, None)
            else (C, Some (L, C), None))
      | L' # _ \<Rightarrow>
        (TWL_Clause (L' # remove1 (-L) (watched C)) (-L # remove1 L' (unwatched C)), None, None)
    else
      (C, None, None))"

end
