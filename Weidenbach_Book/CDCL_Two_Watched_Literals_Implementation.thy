(*  Title: Implementation of CDCL with Two Watched Literals
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

section \<open>Implementation for 2 Watched-Literals\<close>

theory CDCL_Two_Watched_Literals_Implementation
imports CDCL_Two_Watched_Literals_Invariant
begin
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
             (* it contains at most one variable, so... *)
           then (C # Cs, Ks)
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

lemma length_Suc_Suc_0: "length S = 2 \<longleftrightarrow> (\<exists>a b. S = [a, b])"
  sorry
lemma XX: "set_mset (remove1_mset (- lit_of l) (mset W)) = set (remove1 (-lit_of L) W)"
apply auto
sorry
lemma
  assumes
    undef: "undefined L M" and
    "wf_twl_cls M C" and
    n_d: "no_dup (M @ prop_queue Ks)"
  shows "no_dup (prop_queue (snd (rewatch_nat_cand_single_clause L M C (Cs, Ks))))"
  unfolding rewatch_nat_cand_single_clause.simps
  apply (cases Ks; cases C)
  apply (rename_tac M' Confl W UW)
  using undef n_d apply (auto split: list.splits simp: atm_of_eq_atm_of filter_empty_conv
    true_annots_true_cls_def_iff_negation_in_model lits_of_def length_Suc_Suc_0 image_Un
    simp add: XX)

  oops
end