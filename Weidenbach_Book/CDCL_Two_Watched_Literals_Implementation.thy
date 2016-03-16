(*  Title: Implementation of CDCL with Two Watched Literals
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

section \<open>Implementation for 2 Watched-Literals\<close>

theory CDCL_Two_Watched_Literals_Implementation
imports CDCL_Two_Watched_Literals_Invariant
begin
text \<open>The general idea is the following:
  \<^enum> Build a ``propagate'' queue and a conflict clause.
  \<^enum> While updating the data-structure: if you find a conflicting clause, update the conflict
  clause. Otherwise prepend the propagated clause.
  \<^enum> While updating, when looking for conflicts and propagation, work with respect to the
  trail of the state and the propagate queue (and not only the trail of the state).
  \<^enum> As long as the propagate queue is not empty, dequeue the first element, push it on the
  trail (with the @{term conflict_driven_clause_learning\<^sub>W.propagate} rule), propagate, and update
  the data-structure.
  \<^enum> if a conflict has been found such that it is entailed by the trail only (i.e.\ without
  the propagate queue), then apply the @{term conflict_driven_clause_learning\<^sub>W.conflict} rule.\<close>
text \<open>It is important to remember that a conflicting clause with respect to the trail and the queue
  might not be the earliest conflicting clause, meaning that the proof of non-redundancy should not
  work anymore.

  However, once a conflict has been found, we can stop adding literals to the queue: we just have to
  finish updating the data-structure (both to keep the invariant and find a potentially better
  conflict). A conflict is better when it involves less literals, i.e.\ less propagations before
  finding the conflict.\<close>
datatype 'v candidate =
  Prop_Or_Conf
    (prop_queue: "('v, nat, 'v twl_clause) marked_lit list")
    (conflict: "'v twl_clause option")

datatype 'v twl_state_cands =
  TWL_State_Cand (twl_state: "'v twl_state")
    (cand: "'v candidate")

fun find_earliest_conflict :: "('v, nat, 'v twl_clause) marked_lits \<Rightarrow>
  'v twl_clause \<Rightarrow> 'v twl_clause option \<Rightarrow> 'v twl_clause" where
"find_earliest_conflict _ C None = C" |
"find_earliest_conflict [] C _ = C" |
"find_earliest_conflict (L # M) C (Some D) =
  (case (M \<Turnstile>a mset (raw_clause C), \<not>M\<Turnstile>a mset (raw_clause D)) of
    (True, True) \<Rightarrow> find_earliest_conflict M C (Some D)
  | (False, True) \<Rightarrow> D
  | (True, False) \<Rightarrow> C
  | _ \<Rightarrow> C)"

lemma find_earliest_conflict_cases:
  "find_earliest_conflict M C (Some D) = C \<or> find_earliest_conflict M C (Some D) = D"
  by (induction M) (auto split: bool.splits)
  
text \<open>While updating the clauses, there are several cases:
  \<^item> @{term L} is not watched and there is nothing to do;
  \<^item> there is a literal to be watched: there are swapped;
  \<^item> there is no literal to be watched, the other literal is not assigned: the clause
  is a propagate or a conflict candidate;
  \<^item> there is no literal to be watched, but the other literal is true: there is nothing to
  do;
  \<^item> there is no literal to be watched, but the other literal is false: the clause is a
  conflict candidate.\<close>
fun
  rewatch_nat_cand_single_clause ::
  "'v literal \<Rightarrow> ('v, nat, 'v twl_clause) marked_lits \<Rightarrow> 'v twl_clause \<Rightarrow>
    'v twl_clause list \<times> 'v candidate \<Rightarrow>
     'v twl_clause list  \<times> 'v candidate"
where
"rewatch_nat_cand_single_clause L M C (Cs, Ks) =
  (if - L \<in> set (watched C) then
     case filter (\<lambda>L'. L' \<notin> set (watched C) \<and> - L' \<notin> insert L (lits_of_l M))
        (unwatched C) of
       [] \<Rightarrow>
         (if M @ prop_queue Ks \<Turnstile>as CNot (mset (remove1 (-L) (watched C)))
         then (C # Cs, Prop_Or_Conf (prop_queue Ks)
           (Some (find_earliest_conflict M C (conflict Ks))))
         else
           if set (remove1 (-L) (watched C)) \<subseteq> lits_of_l (M @ prop_queue Ks)
             (* it contains at most one variable, so it is easy to do in practice *)
           then (if conflict Ks = None then C # Cs else Cs, Ks)
           else (C # Cs, Prop_Or_Conf (Propagated L C # prop_queue Ks) (conflict Ks)))
     | L' # _ \<Rightarrow>
       (TWL_Clause (L' # remove1 (-L) (watched C)) (-L # remove1 L' (unwatched C)) # Cs, Ks)
  else
    (C # Cs, Ks))"

declare rewatch_nat_cand_single_clause.simps[simp del]

fun rewatch_nat_cand :: "'a literal \<Rightarrow> 'a twl_state_cands \<Rightarrow> 'a twl_state_cands"  where
"rewatch_nat_cand L (TWL_State_Cand S Ks) =
  (let update = \<lambda>Cs Ks. foldr (rewatch_nat_cand_single_clause L (raw_trail S)) Cs ([], Ks);
    (N, K) = update (raw_init_clss S) Ks;
    (U, K') = update (raw_learned_clss S) K in
  TWL_State_Cand
    (TWL_State (raw_trail S) N U (backtrack_lvl S) (raw_conflicting S))
    K')"
lemmas XX = imageI["of" _ "set _" "(\<lambda>l. atm_of (lit_of l))"]

lemma no_dup_rewatch_nat_cand_single_clause:
  fixes L :: "'v literal"
  assumes
    L: "L \<in> lits_of_l M" and
    wf: "wf_twl_cls M C" and
    n_d: "no_dup (M @ prop_queue Ks)"
  shows "no_dup (M @ prop_queue (snd (rewatch_nat_cand_single_clause L M C (Cs, Ks))))"
  unfolding rewatch_nat_cand_single_clause.simps
  apply (cases Ks; cases C)
  apply (rename_tac M' Confl W UW)
  using L n_d wf apply (auto split: list.splits simp: length_list_2 defined_lit_map
    atm_of_eq_atm_of lits_of_def image_Un dest: XX)

  apply (drule imageI["of" _ "set _" "(\<lambda>l. atm_of (lit_of l))"])
proof -
  fix M' :: "('v, nat, 'v twl_clause) marked_lit list" and UW :: "'v literal list" and l :: "('v, nat, 'v twl_clause) marked_lit" and a :: "'v literal"
  assume a1: "lit_of l \<in> lits_of_l M"
  assume a2: "(\<lambda>l. atm_of (lit_of l)) ` set M \<inter> (\<lambda>l. atm_of (lit_of l)) ` set M' = {}"
  assume a3: "L = lit_of l"
  assume a4: "atm_of (lit_of l) \<in> (\<lambda>l. atm_of (lit_of l)) ` set M'"
  have "L \<in> lit_of ` set M"
    using a3 a1 lits_of_def by blast
  then show False
    using a4 a3 a2 by (metis (no_types) IntI XX empty_iff imageE)
next
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  apply (auto simp add: lits_of_def dest: imageI["of" _ "set _" "(\<lambda>l. atm_of (lit_of l))"])[]
proof -
  fix M' :: "('a, nat, 'a twl_clause) marked_lit list" and UW :: "'a literal list" and l :: "('a, nat, 'a twl_clause) marked_lit" and a :: "'a literal" and x :: "('a, nat, 'a twl_clause) marked_lit"
  assume a1: "l \<in> set M'"
  assume a2: "L = lit_of x"
  assume a3: "x \<in> set M"
  assume a4: "lit_of l = lit_of x"
  assume "(\<lambda>l. atm_of (lit_of l)) ` set M \<inter> (\<lambda>l. atm_of (lit_of l)) ` set M' = {}"
  then have "atm_of L \<notin> (\<lambda>m. atm_of (lit_of m)) ` set M"
    using a4 a2 a1 by (metis (no_types) IntI empty_iff imageI["of" _ _ "(\<lambda>l. atm_of (lit_of l))"]) (* 154 ms *)
  then show False
    using a3 a2 by blast (* 3 ms *)
next
  
oops  

lemma 
  assumes
    undef: "undefined_lit (M @ prop_queue Ks) L" and
    wf: "wf_twl_cls M C" and
    "conflict Ks = Some D" and 
    "conflict (snd (rewatch_nat_cand_single_clause L M C (Cs, Ks))) = Some D'" and
    n_d: "M @ prop_queue Ks \<Turnstile>as CNot (mset (raw_clause D))"
  shows "M @ prop_queue Ks \<Turnstile>as CNot (mset (raw_clause D'))"
  apply (cases Ks; cases C)
  apply (rename_tac M' Confl W UW)
  using assms find_earliest_conflict_cases[of M C D] 
  apply (auto split: list.splits if_splits simp: length_list_2 defined_lit_map
    rewatch_nat_cand_single_clause.simps raw_clause_def) 
oops
end