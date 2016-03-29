(*  Title: Implementation of CDCL with Two Watched Literals
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

subsection \<open>Implementation for 2 Watched-Literals\<close>

theory CDCL_Two_Watched_Literals_Implementation
imports CDCL_Two_Watched_Literals_Invariant
begin
text \<open>The difference between an implementation and the core described in the previous sections are
  the following:
  \<^item> the candidates are cached while updating the datastructure.
  \<^item> instead of updating with respect to the trail only, we update with respect to the trail \<^emph>\<open>and\<close>
  the candidates (referred as propagate queue later).\<close>
text \<open>The latter change means that we do not do the propagation as single steps where the state
  well-founded as described in the previous paragraph, but we do all the propagation and identify
  the propagation \<^emph>\<open>before\<close> the invariants folds again.

  The general idea is the following:
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
  conflict). A conflict is better when it involves less literals, i.e.\ less propagations are needed
  before finding the conflict.\<close>
datatype 'v candidate =
  Prop_Or_Conf
    (prop_queue: "('v literal \<times> 'v twl_clause) list")
    (conflict: "'v twl_clause option")

text \<open>Morally instead of @{typ "('v literal \<times> 'v twl_clause) list"}, we should use
  @{typ "('v, nat, 'v twl_clause) marked_lits"} with only @{term Propagated}. However, we do not
  want to define the function for @{term Marked} too. The following function makes the conversion
  from the pair to the trail:
  \<close>
abbreviation get_trail_of_cand where
"get_trail_of_cand C \<equiv> map (case_prod Propagated) (prop_queue C)"

datatype 'v twl_state_cands =
  TWL_State_Cand (twl_state: "'v twl_state")
    (cand: "'v candidate")

fun raw_cons_trail where
"raw_cons_trail L (TWL_State M N U k C) = TWL_State (L # M) N U k C"

lemma length_raw_trail_raw_cons_trails[simp]:
  "length (raw_trail (raw_cons_trail (Propagated L C') S)) = Suc (length (raw_trail S))"
  by (cases S) auto

lemma twl_raw_clauses_raw_cons_trail[simp]:
  "twl.raw_clauses (raw_cons_trail (Propagated L C') S) = twl.raw_clauses S"
  by (cases S) (auto simp: twl.raw_clauses_def)

fun raw_cons_trail_pq where
"raw_cons_trail_pq L (TWL_State_Cand S Q) = TWL_State_Cand (raw_cons_trail L S) Q"

fun update_conflicting_pq where
"update_conflicting_pq L (TWL_State_Cand S Q) = TWL_State_Cand (update_conflicting L S) Q"

lemma raw_trail_raw_cons_trail[simp]:
  "raw_trail (raw_cons_trail L S) = L # raw_trail S"
  by (cases S) auto

fun find_earliest_conflict :: "('v, nat, 'v twl_clause) marked_lits \<Rightarrow>
  'v twl_clause option \<Rightarrow> 'v twl_clause option \<Rightarrow> 'v twl_clause option" where
"find_earliest_conflict _ None C = C" |
"find_earliest_conflict _ C None = C" |
"find_earliest_conflict [] C _ = C" |
"find_earliest_conflict (L # M) (Some C) (Some D) =
  (case (M \<Turnstile>a mset (raw_clause C), \<not>M\<Turnstile>a mset (raw_clause D)) of
    (True, True) \<Rightarrow> find_earliest_conflict M (Some C) (Some D)
  | (False, True) \<Rightarrow> Some D
  | (True, False) \<Rightarrow> Some C
  | _ \<Rightarrow> Some C)"

lemma find_earliest_conflict_cases:
  "find_earliest_conflict M (Some C) (Some D) = Some C \<or>
   find_earliest_conflict M (Some C) (Some D) = Some D"
  by (induction M) (auto split: bool.splits)

text \<open>Useful function to chose the first non-@{term None} between two elements.\<close>
notation Quickcheck_Exhaustive.orelse (infixr "orelse" 55)

text \<open>Once a conflict has been found we do not need to add element to the trail of the list.\<close>
fun cons_if_no_conflict where
"cons_if_no_conflict K C Cs Ks =
  (if conflict Ks = None
  then (C # Cs, Prop_Or_Conf (K # prop_queue Ks) (conflict Ks))
  else (C # Cs, Prop_Or_Conf (prop_queue Ks) (conflict Ks)))"

text \<open>While updating the clauses, there are several cases:
  \<^item> @{term L} is not watched and there is nothing to do;
  \<^item> there is a literal to be watched: there are swapped;
  \<^item> there is no literal to be watched, the other literal is not assigned: the clause
  is a propagate or a conflict candidate;
  \<^item> there is no literal to be watched, the other literal is @{term "-L"}: the clause
  is a tautology and nothing special is done;
  \<^item> there is no literal to be watched, but the other literal is true: there is nothing to
  do;
  \<^item> there is no literal to be watched, but the other literal is false: the clause is a
  conflict candidate.

  The function returns a couple composed of a list of clauses and a candidate.\<close>fun
  rewatch_nat_cand_single_clause ::
  "'v literal \<Rightarrow> ('v, nat, 'v twl_clause) marked_lits \<Rightarrow> 'v twl_clause \<Rightarrow>
    'v twl_clause list \<times> 'v candidate \<Rightarrow>
     'v twl_clause list  \<times> 'v candidate"
where
"rewatch_nat_cand_single_clause L M C (Cs, Ks) =
  (if - L \<in> set (watched C) then
     case filter (\<lambda>L'. L' \<notin> set (watched C) \<and>
       - L' \<notin> insert L (lits_of_l (M @ get_trail_of_cand Ks))) (unwatched C) of
       [] \<Rightarrow>
         (case remove1 (-L) (watched C) of (* contains at most a single element *)
             [] \<Rightarrow> (C # Cs, Prop_Or_Conf (prop_queue Ks) (conflict Ks orelse Some C))
           | L' # _ \<Rightarrow>
             if undefined_lit (get_trail_of_cand Ks @ M) L' \<and> atm_of L \<noteq> atm_of L'
             then cons_if_no_conflict (L', C) C Cs Ks
             else
               (if -L' \<in> lits_of_l (get_trail_of_cand Ks @ M)
               then (C # Cs, Prop_Or_Conf (prop_queue Ks) (conflict Ks orelse Some C))
               else (C # Cs, Ks)))
     | L' # _ \<Rightarrow>
       (TWL_Clause (L' # remove1 (-L) (watched C)) (-L # remove1 L' (unwatched C)) # Cs, Ks)
  else
    (C # Cs, Ks))"

declare rewatch_nat_cand_single_clause.simps[simp del]

fun \<mu>TWL where
"\<mu>TWL (TWL_State_Cand U (Prop_Or_Conf Q D)) =
  card {C \<in> set_mset (twl.clauses U). \<not>raw_trail U @ get_trail_of_cand (Prop_Or_Conf Q D) \<Turnstile>a C}"

fun
  rewatch_nat_cand_clss ::
  "'v literal \<Rightarrow> ('v, nat, 'v twl_clause) marked_lits \<Rightarrow>
    'v twl_clause list \<times> 'v candidate \<Rightarrow>
     'v twl_clause list  \<times> 'v candidate"
where
"rewatch_nat_cand_clss L M (Cs, Ks) =
  foldr (rewatch_nat_cand_single_clause L M) Cs ([], Ks)"

declare rewatch_nat_cand_clss.simps[simp del]

lemma CNot_mset_replicate[simp]:
  "CNot (mset (replicate n L)) = (if n = 0 then {} else {{#-L#}})"
  by (induction n) auto

lemma wf_rewatch_nat_cand_single_clause_cases[consumes 1, case_names wf lit_notin propagate conflict
  no_conflict update_cls]:
  assumes
    wf: "wf_twl_cls M C" and
    lit_notin: "-L \<notin> set (watched C) \<Longrightarrow>
      rewatch_nat_cand_single_clause L M C (Cs, Ks) = (C # Cs, Ks) \<Longrightarrow>
      P"
      and
    single_lit_watched: "
      -L \<in> set (watched C) \<Longrightarrow>
      filter (\<lambda>L'. L' \<notin> set (watched C) \<and>
        - L' \<notin> insert L (lits_of_l (M @ get_trail_of_cand Ks))) (unwatched C) = [] \<Longrightarrow>
      watched C = [-L] \<Longrightarrow>
      set (unwatched C) \<subseteq> {-L} \<Longrightarrow>
      rewatch_nat_cand_single_clause L M C (Cs, Ks) =
        (C # Cs, Prop_Or_Conf (prop_queue Ks) (conflict Ks orelse Some C)) \<Longrightarrow>
      P"
      and
    propagate: "\<And>L'. -L \<in> set (watched C) \<Longrightarrow>
      filter (\<lambda>L'. L' \<notin> set (watched C) \<and>
        - L' \<notin> insert L (lits_of_l (M @ get_trail_of_cand Ks))) (unwatched C) = [] \<Longrightarrow>
      set (watched C) = {-L, L'} \<Longrightarrow>
      undefined_lit (get_trail_of_cand Ks @ M) L' \<Longrightarrow>
      atm_of L \<noteq> atm_of L' \<Longrightarrow>
      rewatch_nat_cand_single_clause L M C (Cs, Ks) = cons_if_no_conflict (L', C) C Cs Ks \<Longrightarrow>
      P"
      and
    conflict: "\<And>L'. -L \<in> set (watched C) \<Longrightarrow>
      filter (\<lambda>L'. L' \<notin> set (watched C) \<and>
        - L' \<notin> insert L (lits_of_l (M @ get_trail_of_cand Ks))) (unwatched C) = [] \<Longrightarrow>
      set (watched C) = {-L, L'} \<Longrightarrow>
      -L' \<in> insert L (lits_of_l (get_trail_of_cand Ks @ M)) \<Longrightarrow>
      rewatch_nat_cand_single_clause L M C (Cs, Ks) =
        (C # Cs, Prop_Or_Conf (prop_queue Ks) (conflict Ks orelse Some C)) \<Longrightarrow>
      P"
      and
    no_conflict: "\<And>L'. -L \<in> set (watched C) \<Longrightarrow>
      filter (\<lambda>L'. L' \<notin> set (watched C) \<and>
        - L' \<notin> insert L (lits_of_l (M @ get_trail_of_cand Ks))) (unwatched C) = [] \<Longrightarrow>
      set (watched C) = {-L, L'} \<Longrightarrow>
      L' \<in> insert L (lits_of_l (get_trail_of_cand Ks @ M)) \<Longrightarrow>
      rewatch_nat_cand_single_clause L M C (Cs, Ks) = (C # Cs, Ks) \<Longrightarrow>
      P"
      and
    update_cls: "\<And>L' fUW. -L \<in> set (watched C) \<Longrightarrow>
      filter (\<lambda>L'. L' \<notin> set (watched C) \<and>
        - L' \<notin> insert L (lits_of_l (M @ get_trail_of_cand Ks))) (unwatched C) = L' # fUW
        \<Longrightarrow>
      rewatch_nat_cand_single_clause L M C (Cs, Ks) =
        (TWL_Clause (L' # remove1 (-L) (watched C)) (-L # remove1 L' (unwatched C)) # Cs, Ks) \<Longrightarrow>
      P"
  shows P
proof -
  show ?thesis
    proof (cases "- L \<notin> set (watched C)")
      case l: True
      then show ?thesis
        by (rule lit_notin; auto simp add: rewatch_nat_cand_single_clause.simps)
    next
      case False
      then have L: "- L \<in> set (watched C)"
        by blast
      show ?thesis
        proof (cases "filter (\<lambda>L'. L' \<notin> set (watched C) \<and>
          - L' \<notin> insert L (lits_of_l (M @ get_trail_of_cand Ks)))
          (unwatched C)")
          case (Cons L' fUW)
          then show ?thesis
            apply - by (rule update_cls; auto simp add: rewatch_nat_cand_single_clause.simps L)
        next
          case filter: Nil
          then show ?thesis
            proof (cases "remove1 (-L) (watched C)")
              case Nil
              then show ?thesis apply -
                apply (rule single_lit_watched; cases C)
                using wf L filter by (auto simp: rewatch_nat_cand_single_clause.simps length_list_2
                  remove1_nil)[5]
            next
              case (Cons L' fW)
              then have dist: "distinct (watched C)" and l_W: "length (watched C) \<le> 2"
                using wf by (cases C, auto)+
              then have [simp]: "fW = []" using Cons
                by (metis L One_nat_def Suc_1 Suc_eq_plus1 add_diff_cancel_left' add_right_imp_eq
                  diff_is_0_eq le_Suc_eq length_0_conv length_remove1 list.distinct(1) list.size(4))
              then have C: "set (watched C) = {-L, L'}"
                using l_W L dist arg_cong[OF Cons, of set, simplified] by auto
              have [simp]: "remove1 L' (watched C) \<noteq> [L']"
                by (metis DiffD2 dist insertI1 list.simps(15) set_remove1_eq)
              show ?thesis
                apply (cases "undefined_lit (get_trail_of_cand Ks @ M) L'\<and> atm_of L \<noteq> atm_of L' ")
                apply (rule propagate)
                  using L filter C Cons dist
                  apply (auto simp: rewatch_nat_cand_single_clause.simps atm_of_eq_atm_of)[6]
                apply (cases "-L' \<in> insert L (lits_of_l (get_trail_of_cand Ks @ M))")
                apply (rule conflict)
                  using L filter C Cons apply (auto simp: rewatch_nat_cand_single_clause.simps)[5]
                  apply (rule no_conflict)
                  using L filter C Cons apply (auto simp: rewatch_nat_cand_single_clause.simps
                    defined_lit_map lits_of_def image_Un atm_of_eq_atm_of image_image
                    rev_image_eqI)[5]
                done
            qed
        qed
    qed
qed

lemma prop_queue_rewatch_nat_cand_single_clause_eq_or_cons:
  "prop_queue (snd (rewatch_nat_cand_single_clause L M C S)) = prop_queue (snd S) \<or>
  (\<exists>L'. prop_queue (snd (rewatch_nat_cand_single_clause L M C S)) = L' # prop_queue (snd S))"
  apply (cases C, cases S)
  apply (auto simp: raw_clause_def filter_empty_conv true_annots_true_cls_def_iff_negation_in_model
    comp_def rewatch_nat_cand_single_clause.simps lits_of_def image_image split: list.splits
     simp del: watched_decided_most_recently.simps)
  done

lemmas rewatch_nat_cand_single_clause_cases =
  wf_rewatch_nat_cand_single_clause_cases[OF wf_twl_cls_append[of "get_trail_of_cand _"],
    consumes 2, case_names wf lit_notin propagate conflict no_conflict update_cls]

lemma lit_of_case_Propagated[simp]: "lit_of (case x of (x, xa) \<Rightarrow> Propagated x xa) = fst x"
  by (cases x) auto

fun rewatch_nat_cand :: "'a literal \<Rightarrow> 'a twl_state_cands \<Rightarrow> 'a twl_state_cands"  where
"rewatch_nat_cand L (TWL_State_Cand S Ks) =
  (let
    (N, K) = rewatch_nat_cand_clss L (raw_trail S) (raw_init_clss S, Ks);
    (U, K') = rewatch_nat_cand_clss L (raw_trail S) (raw_learned_clss S, K) in
  TWL_State_Cand
    (TWL_State (raw_trail S) N U (backtrack_lvl S) (raw_conflicting S))
    K')"

lemma rewatch_nat_cand_single_clause_hd:
  "clauses_of_l (map raw_clause (fst (rewatch_nat_cand_single_clause L M C K))) =
      clauses_of_l (map raw_clause (C # (fst K)))"
  apply (cases C, cases K)
  apply (auto simp: raw_clause_def filter_empty_conv true_annots_true_cls_def_iff_negation_in_model
    comp_def rewatch_nat_cand_single_clause.simps lits_of_def image_image split: list.splits
     simp del: watched_decided_most_recently.simps)
  apply (auto dest:filter_in_list_prop_verifiedD simp: multiset_eq_iff)
  done

lemma rewatch_nat_cand_single_clause_clauses:
  "clauses_of_l (map raw_clause (fst (rewatch_nat_cand_clss L M (N, Ks)))) =
      clauses_of_l (map raw_clause N)"
  by (induction N) (simp_all add: rewatch_nat_cand_clss.simps
    rewatch_nat_cand_single_clause_hd[simplified])

lemma prop_queue_rewatch_nat_cand_clss_eq_or_cons:
  "(\<exists>L'. prop_queue (snd (rewatch_nat_cand_clss L M K)) = L' @ prop_queue (snd K))"
proof -
  obtain Cs Q where K: "K = (Cs, Q)"
    by (cases K)
  show ?thesis
    unfolding K
    proof (induction Cs)
      case Nil
      then show ?case
       by (auto simp: rewatch_nat_cand_clss.simps)[]
    next
      case (Cons C Cs)
      then show ?case
        using prop_queue_rewatch_nat_cand_single_clause_eq_or_cons[of L M C
         "foldr (rewatch_nat_cand_single_clause L M) Cs ([], Q)"]
         by (auto simp: rewatch_nat_cand_clss.simps)
    qed
qed

lemma prop_queue_rewatch_nat_cand_eq_or_cons:
  "(\<exists>L'. prop_queue (cand (rewatch_nat_cand L S)) = L' @ prop_queue (cand S))"
proof -
  obtain T Ks where S: "S = TWL_State_Cand T Ks"
    by (cases S)
  obtain U K' where
    U: "rewatch_nat_cand_clss L (raw_trail T) (raw_init_clss T, Ks) = (U, K')"
    (is "?H = _") by (cases ?H)

  obtain V K'' where
    V: "rewatch_nat_cand_clss L (raw_trail T) (raw_learned_clss T, K') = (V, K'')"
    (is "?H = _") by (cases ?H)

  show ?thesis unfolding S
    using prop_queue_rewatch_nat_cand_clss_eq_or_cons[of L "raw_trail T" "(raw_init_clss T, Ks)"]
    using prop_queue_rewatch_nat_cand_clss_eq_or_cons[of L "raw_trail T" "(raw_learned_clss T, K')"]
    by (auto simp: comp_def twl.raw_clauses_def U V)
qed

lemma "twl.clauses (twl_state (rewatch_nat_cand L S)) = twl.clauses (twl_state S)"
proof -
  obtain T Ks where S: "S = TWL_State_Cand T Ks"
    by (cases S)
  obtain U K' where
    U: "rewatch_nat_cand_clss L (raw_trail T) (raw_init_clss T, Ks) = (U, K')"
    (is "?H = _") by (cases ?H)

  obtain V K'' where
    V: "rewatch_nat_cand_clss L (raw_trail T) (raw_learned_clss T, K') = (V, K'')"
    (is "?H = _") by (cases ?H)

  have "mset (map (\<lambda>x. mset (raw_clause x)) U) = mset (map (\<lambda>x. mset (raw_clause x)) (raw_init_clss T))"
    using rewatch_nat_cand_single_clause_clauses[of L "raw_trail T" "raw_init_clss T"
      "Ks"] by (auto simp: comp_def U)
  moreover have "mset (map (\<lambda>x. mset (raw_clause x)) V) = mset (map (\<lambda>x. mset (raw_clause x))
  (raw_learned_clss T))"
    using rewatch_nat_cand_single_clause_clauses[of L "raw_trail T" "raw_learned_clss T"
      "K'"] by (auto simp: comp_def V)
  ultimately show ?thesis  unfolding S
    by (auto simp: comp_def twl.raw_clauses_def U V)
qed

(* TODO Move me *)
lemma raw_init_clss_raw_cons_trail[simp]:
  "raw_init_clss (raw_cons_trail L T) = raw_init_clss T"
  by (cases T) auto

lemma raw_learned_clss_raw_cons_trail[simp]:
  "raw_learned_clss (raw_cons_trail L T) = raw_learned_clss T"
  by (cases T) auto
(* END Move Me *)

lemma true_annot_mono_append_append:
  "A @ C \<Turnstile>a D \<Longrightarrow>  A @ B @ C \<Turnstile>a D"
  "A @ C \<Turnstile>a D \<Longrightarrow>  L # A @ B @ C \<Turnstile>a D"
  by (rule true_annot_mono; auto)+

lemma true_annot_mono':
  "\<not>I' \<Turnstile>a N \<Longrightarrow> I \<Turnstile>a N \<Longrightarrow> \<not>set I \<subseteq> set I' "
  using true_annot_mono by blast

lemma YYY:
  "\<mu>TWL (raw_cons_trail_pq (Propagated L C')
    (rewatch_nat_cand L (TWL_State_Cand S (Prop_Or_Conf Q D))))
   \<le> \<mu>TWL (TWL_State_Cand S (Prop_Or_Conf (Q @ [(L, C')]) D))"
proof -
  obtain U K' where
    U: "rewatch_nat_cand_clss L (raw_trail S) (raw_init_clss S, Prop_Or_Conf Q D) = (U, K')"
    (is "?H = _") by (cases ?H)

  obtain V K'' where
    V: "rewatch_nat_cand_clss L (raw_trail S) (raw_learned_clss S, K') = (V, K'')"
    (is "?H = _") by (cases ?H)

  obtain Q'' D'' where K'': "K'' = Prop_Or_Conf Q'' D''"
    by (cases K'')
  obtain P where P: "Q'' = P @ Q"
    using prop_queue_rewatch_nat_cand_eq_or_cons[of L "TWL_State_Cand S (Prop_Or_Conf Q D)"]
    by (auto simp: comp_def twl.raw_clauses_def U V K'')

  have H1: "set_mset (mset (map (\<lambda>t. mset (raw_clause t)) U)) =
    (\<lambda>t. mset (raw_clause t)) ` set_mset (mset (raw_init_clss S))"
    using rewatch_nat_cand_single_clause_clauses[of L "raw_trail S" "raw_init_clss S"
      "Prop_Or_Conf Q D"] by (auto simp: comp_def U)
  moreover
    have H2: "set_mset (mset (map (\<lambda>t. mset (raw_clause t)) V)) =
      (\<lambda>t. mset (raw_clause t)) ` set_mset (mset (raw_learned_clss S))"
      using rewatch_nat_cand_single_clause_clauses[of L "raw_trail S" "raw_learned_clss S"
        "K'"] by (auto simp: comp_def V)
  ultimately
    have "card ((\<lambda>x. mset (raw_clause x)) ` set (raw_init_clss S)
      \<union> (\<lambda>x. mset (raw_clause x)) ` set (raw_learned_clss S)) =
      card ((\<lambda>x. mset (raw_clause x)) ` set U \<union> (\<lambda>x. mset (raw_clause x)) ` set V)"
      by simp
  moreover
    have
      "card {C. C \<in> (\<lambda>x. mset (raw_clause x)) ` set (twl.raw_clauses S) \<and>
         \<not>(Propagated L C') # raw_trail S @ map (\<lambda>(x, y). Propagated x y) Q'' \<Turnstile>a C}
    \<le> card {C. C \<in> (\<lambda>x. mset (raw_clause x)) ` set (twl.raw_clauses S) \<and>
         \<not>raw_trail S @ map (\<lambda>(x, y). Propagated x y) Q @ [Propagated L C'] \<Turnstile>a C}"
    apply (rule card_mono)
    apply (auto)
    (* TODO Proof *)
    apply (drule true_annot_mono')
    apply (auto simp: P)[2]
    done
  moreover
    have "(\<lambda>x. mset (raw_clause x)) ` set (twl.raw_clauses
       (TWL_State (Propagated L C' # raw_trail S) U V (backtrack_lvl S) (raw_conflicting S))) =
     (\<lambda>x. mset (raw_clause x)) ` set (twl.raw_clauses S)"
     using H1 H2 by (auto simp: twl.raw_clauses_def)
  ultimately show ?thesis
    by (auto simp: comp_def U V K'' intro!: Nat.diff_le_mono2)
qed



text \<open>Implementation-wise, @{term "trail S \<Turnstile>as CNot (mset (raw_clause D))"} should be equivalent
  to there is no more propagation to do.\<close>
function do_propagate_or_conflict_step :: "'a twl_state_cands \<Rightarrow> 'a twl_state_cands" where
"do_propagate_or_conflict_step (TWL_State_Cand S (Prop_Or_Conf [] (Some D))) =
  (if trail S \<Turnstile>as CNot (mset (raw_clause D))
  then (update_conflicting_pq (Some (raw_clause D)) (TWL_State_Cand S (Prop_Or_Conf [] None)))
  else TWL_State_Cand S (Prop_Or_Conf [] (Some D)))" |
"do_propagate_or_conflict_step (TWL_State_Cand S (Prop_Or_Conf [] None)) =
  TWL_State_Cand S (Prop_Or_Conf [] None)" |
"do_propagate_or_conflict_step (TWL_State_Cand S (Prop_Or_Conf (l @ [(L, C')]) (Some D))) =
  (if trail S \<Turnstile>as CNot (mset (raw_clause D))
  then update_conflicting_pq (Some (raw_clause D)) (TWL_State_Cand S (Prop_Or_Conf l None))
  else do_propagate_or_conflict_step
    (raw_cons_trail_pq (Propagated L C')
      (rewatch_nat_cand L (TWL_State_Cand S (Prop_Or_Conf l (Some D))))))" |
"do_propagate_or_conflict_step (TWL_State_Cand S (Prop_Or_Conf (l @ [(L, C')]) None)) =
  do_propagate_or_conflict_step
    (raw_cons_trail_pq (Propagated L C')
      (rewatch_nat_cand L (TWL_State_Cand S (Prop_Or_Conf l None))))"
  apply (rename_tac P x)
  apply (case_tac x, case_tac "cand x"; case_tac "conflict (cand x)";
    case_tac "prop_queue (cand x)" rule: rev_cases; simp)
  by auto
termination
  apply (relation "{(T, S).
    ([\<mu>TWL T, length (prop_queue (cand T))], [\<mu>TWL S, length (prop_queue (cand S))])
    \<in> lexn less_than 2}")
proof (goal_cases)
  case 1
  show ?case by (auto simp: wf_lexn intro!: wf_if_measure_f)
next
  case (2 S l L C' D)
  show ?case
    using YYY[of L C' S l "Some D"]
    apply (auto simp add: comp_def lexn_n simp del: lexn.simps(2) rewatch_nat_cand.simps
      \<mu>TWL.simps)

    sorry
next
  case (3 S l L C')
  show ?case
    by (auto simp add: comp_def lexn_n true_annot_def simp del: lexn.simps(2))
qed

lemma no_dup_rewatch_nat_cand_single_clause:
  fixes L :: "'v literal"
  assumes
    L: "L \<in> lits_of_l M" and
    wf: "wf_twl_cls (get_trail_of_cand Ks @ M) C" and
    n_d: "no_dup (get_trail_of_cand Ks @ M)"
  shows "no_dup (M @ get_trail_of_cand (snd (rewatch_nat_cand_single_clause L M C (Cs, Ks))))"
  using n_d wf apply (cases rule: rewatch_nat_cand_single_clause_cases[of Ks M C L Cs Ks])
  using L n_d by (auto simp: defined_lit_map comp_def image_image image_Un)


lemma wf_twl_cls_prop_in_trailD:
  assumes "wf_twl_cls M (TWL_Clause W UW)"
  shows "\<forall>L \<in> set W. -L \<in> lits_of_l M \<longrightarrow> (\<forall>L' \<in> set UW. L' \<notin> set W \<longrightarrow> -L' \<in> lits_of_l M)"
  using assms by auto

lemma rewatch_nat_cand_single_clause_conflict:
  assumes
    L: "L \<in> lits_of_l M" and
    wf: "wf_twl_cls (get_trail_of_cand Ks @ M) C" and
    conf: "conflict Ks = Some D" and
    conf': "conflict (snd (rewatch_nat_cand_single_clause L M C (Cs, Ks))) = Some D'" and
    n_d: "no_dup (get_trail_of_cand Ks @ M)" and
    confI: "get_trail_of_cand Ks @ M \<Turnstile>as CNot (mset (raw_clause D))"
  shows "get_trail_of_cand Ks @ M \<Turnstile>as CNot (mset (raw_clause D'))"
  apply (cases C)
  using n_d wf apply (cases rule: rewatch_nat_cand_single_clause_cases[of Ks M C L Cs Ks])
  prefer 4
    using conf conf' confI L find_earliest_conflict_cases[of "get_trail_of_cand Ks @ M" C D] wf
    apply (fastforce simp add: raw_clause_def true_annots_true_cls_def_iff_negation_in_model
        simp del: watched_decided_most_recently.simps wf_twl_cls.simps
        dest!: wf_twl_cls_prop_in_trailD)[]
  using conf conf' confI L find_earliest_conflict_cases[of "get_trail_of_cand Ks @ M" C D]
  apply (auto simp add: raw_clause_def  true_annots_true_cls_def_iff_negation_in_model
      simp del: watched_decided_most_recently.simps
    )[5]
  done

lemma rewatch_nat_cand_single_clause_conflict_found:
  assumes
    L: "L \<in> lits_of_l M" and
    wf: "wf_twl_cls (get_trail_of_cand Ks @ M) C" and
    n_d: "no_dup (get_trail_of_cand Ks @ M)" and
    conf: "conflict Ks = None" and
    conf': "conflict (snd (rewatch_nat_cand_single_clause L M C (Cs, Ks))) = Some D'"
  shows "get_trail_of_cand Ks @ M \<Turnstile>as CNot (mset (raw_clause D'))"
  apply (cases C)
  using n_d wf apply (cases rule: rewatch_nat_cand_single_clause_cases[of Ks M C L Cs Ks])
  using conf conf' L
  by (auto simp add: raw_clause_def filter_empty_conv true_annots_true_cls_def_iff_negation_in_model
     simp del: watched_decided_most_recently.simps)


text \<open>This lemma is \<^emph>\<open>wrong\<close>: we are speaking of half-update data-structure, meaning that
  @{term "wf_twl_cls (get_trail_of_cand K @ M) C"} is the wrong assumption to use.\<close>
lemma
  fixes Ks :: "'v candidate" and M :: "('v, nat, 'v twl_clause) marked_lit list"
  and L :: "'v literal" and Cs :: "'v twl_clause list" and C :: "'v twl_clause"
  defines "S \<equiv> rewatch_nat_cand_single_clause L M C (Cs, Ks)"
  assumes wf: "wf_twl_cls (get_trail_of_cand Ks @ M) C" and
    n_d: "no_dup (get_trail_of_cand Ks @ M)"
  shows "wf_twl_cls (get_trail_of_cand (snd S) @ M) C"
proof -
  obtain W UW where C: "C = TWL_Clause W UW"
    by (cases C)

  show ?thesis
    using n_d wf
    proof (cases rule: rewatch_nat_cand_single_clause_cases[of Ks M C L Cs Ks])
      case lit_notin
      show ?thesis
        using wf unfolding S_def lit_notin by simp
    next
      case (propagate L') note L = this(1) and filter = this(2) and wC = this(3) and uC = this(4)
        and rewatch = this(6)
      show ?thesis
        using wf filter wC uC unfolding S_def rewatch unfolding C wf_twl_cls.simps Ball_def
        apply (intro allI conjI impI)
              apply (auto simp add: C simp del: watched_decided_most_recently.simps)[3]
         apply (auto simp add: filter_empty_conv uminus_lit_swap)[]
        apply (auto simp add: filter_empty_conv Marked_Propagated_in_iff_in_lits_of_l lits_of_def
           image_Un Ball_def)[]
         done
    next
      case (conflict L') note L = this(1) and filter = this(2) and wC = this(3) and uC = this(4) and
       rewatch = this(5)
       show ?thesis
         using wf filter wC uC unfolding S_def rewatch unfolding C wf_twl_cls.simps Ball_def
         apply (intro allI conjI impI)
         apply (auto simp add: C filter_empty_conv Marked_Propagated_in_iff_in_lits_of_l lits_of_def
           image_Un simp del: watched_decided_most_recently.simps)
         done
    next
      case (no_conflict L') note L = this(1) and filter = this(2) and wC = this(3) and uC = this(4)
        and rewatch = this(5)
       show ?thesis
         using wf filter wC uC unfolding S_def rewatch unfolding C wf_twl_cls.simps Ball_def
         apply (intro allI conjI impI)
         apply (auto simp add: C filter_empty_conv uminus_lit_swap lits_of_def image_Un
          simp del: watched_decided_most_recently.simps)
         done
    next
      case (update_cls L') note L = this(1) and filter = this(2) and rewatch = this(3)
       show ?thesis
         using wf filter unfolding S_def rewatch unfolding C wf_twl_cls.simps Ball_def
         apply (intro allI conjI impI)
         apply (auto simp add: C  filter_empty_conv uminus_lit_swap lits_of_def image_Un
           image_image comp_def
          simp del: watched_decided_most_recently.simps)
         done
    next
      case t: wf
      then show ?thesis
        using wf unfolding S_def by simp
    qed
qed
(*
lemma wf_rewatch_nat_cand_single_clause:
  fixes Ks :: "'v candidate" and M :: "('v, nat, 'v twl_clause) marked_lit list" and
    L :: "('v, nat, 'v twl_clause) marked_lit" and Cs :: "'v twl_clause list" and
    C :: "'v twl_clause"
  defines "S \<equiv> rewatch_nat_cand_single_clause (lit_of L) M C (Cs, Ks)"
  assumes
    wf: "wf_twl_cls (get_trail_of_cand Ks @ M) C" and
    n_d: "no_dup (get_trail_of_cand Ks @ M)" and
    undef: "undefined_lit (get_trail_of_cand Ks @ M) (lit_of L)"
  shows "wf_twl_cls (get_trail_of_cand Ks @ L # M) (hd (fst S))"
proof -
  obtain W UW where C: "C = TWL_Clause W UW"
    by (cases C)
  have t: "watched_decided_most_recently (get_trail_of_cand Ks @ M) (TWL_Clause W UW)" and
    wf': "distinct W \<and> length W \<le> 2 \<and> (length W < 2 \<longrightarrow> set UW \<subseteq> set W)" and
    H: "\<forall>L \<in> set W. -L \<in> lits_of_l (get_trail_of_cand Ks @ M) \<longrightarrow>
      (\<forall>L' \<in> set UW. L' \<notin> set W \<longrightarrow> -L' \<in> lits_of_l (get_trail_of_cand Ks @ M))"
    using wf unfolding C by (auto simp add: comp_def lits_of_def image_image image_Un)
  show ?thesis
    using wf
    proof (cases rule: wf_rewatch_nat_cand_single_clause_cases[of M C "lit_of L" Cs Ks])
      case lit_notin
      show ?thesis
        using wf' unfolding S_def lit_notin unfolding C apply simp
        using C lit_notin by auto
    next
      case propagate note L = this(1) and filter = this(2) and wC = this(3) and uC = this(4) and
       rewatch = this(6)
      show ?thesis
        using wf' filter wC uC unfolding S_def rewatch unfolding C wf_twl_cls.simps Ball_def
        fst_conv  List.list.sel(1)
        apply (intro allI conjI impI)
              apply (auto simp add: C simp del: watched_decided_most_recently.simps)[3]
         apply (auto simp add: filter_empty_conv uminus_lit_swap)[]
        apply (auto simp add: filter_empty_conv Marked_Propagated_in_iff_in_lits_of_l lits_of_def
           image_Un)[]
         done
    next
      case (conflict L') note L = this(1) and filter = this(2) and wC = this(3) and uC = this(4) and
       rewatch = this(5)
       show ?thesis
         using filter wC uC unfolding S_def rewatch unfolding C wf_twl_cls.simps Ball_def fst_conv
          List.list.sel(1)
         apply (intro allI conjI impI)
         using wf' apply (auto simp add: C filter_empty_conv Marked_Propagated_in_iff_in_lits_of_l
           lits_of_def image_Un simp del: watched_decided_most_recently.simps)[4]
         using t apply simp
         done
    next
      case (no_conflict L') note L = this(1) and filter = this(2) and wC = this(3) and uC = this(4)
        and rewatch = this(5)
       show ?thesis
         using filter wC uC unfolding S_def rewatch unfolding C wf_twl_cls.simps Ball_def fst_conv
          List.list.sel(1)
         apply (intro allI conjI impI)
         using wf' apply (auto simp add: C filter_empty_conv uminus_lit_swap lits_of_def image_Un
          simp del: watched_decided_most_recently.simps)[4]
         using t apply simp
         done
    next
      case (update_cls L') note L = this(1) and filter = this(2) and rewatch = this(3)
      show ?thesis
         using filter unfolding S_def rewatch unfolding C wf_twl_cls.simps Ball_def fst_conv
           List.list.sel(1)
         apply (intro allI conjI impI)
         using wf' L apply (auto simp add: C filter_empty_conv uminus_lit_swap lits_of_def
           image_Un length_remove1 subset_iff
          simp del: watched_decided_most_recently.simps dest: filter_in_list_prop_verifiedD)[3]
         using H wf' apply (auto simp add: C  filter_empty_conv uminus_lit_swap lits_of_def
           image_Un length_remove1 subset_iff
          simp del: watched_decided_most_recently.simps dest: filter_in_list_prop_verifiedD
          split: if_split_asm)[]

         using t L wf' H apply (auto simp add: C uminus_lit_swap
          dest: filter_eq_ConsD)[]
         done
    next
      case t: wf note L = this(1) and rewatch = this(2)
      show ?thesis
        using n_d wf L unfolding S_def rewatch unfolding C wf_twl_cls.simps Ball_def fst_conv
           List.list.sel(1) watched_decided_most_recently.simps
         apply (intro allI conjI impI)
           apply (auto simp: uminus_lit_swap)[4]
        apply (rename_tac L' La)
        unfolding list.map index.simps
        apply simp
        apply (intro allI impI conjI)
        defer apply auto[]

        apply (subgoal_tac "defined_lit M (-La)")
        defer unfolding defined_lit_map
          apply (metis atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set atm_of_uminus image_image
            lits_of_def)
        using undef apply (auto simp: defined_lit_map lits_of_def)
        done
    qed
qed
 *)
lemma rewatch_nat_cand_single_clause_no_dup:
  fixes Ks :: "'v candidate" and M :: "('v, nat, 'v twl_clause) marked_lit list"
  and L :: "'v literal" and Cs :: "'v twl_clause list" and C :: "'v twl_clause"
  defines "S \<equiv> rewatch_nat_cand_single_clause L M C (Cs, Ks)"
  assumes wf: "wf_twl_cls M C" and
    n_d: "no_dup (get_trail_of_cand Ks @ M)" and
    undef: "undefined_lit (get_trail_of_cand Ks @ M) L"
  shows "no_dup (get_trail_of_cand (snd S) @ M)"
  using wf n_d apply (cases rule: wf_rewatch_nat_cand_single_clause_cases[of M C L Cs Ks])
  using undef unfolding S_def by (auto simp add: defined_lit_map image_Un image_image comp_def)

(* lemma wf_foldr_rewatch_nat_cand_single_clause:
  fixes Ks :: "'v candidate" and M :: "('v, nat, 'v twl_clause) marked_lits" and
    L :: "('v, nat, 'v twl_clause) marked_lit" and Cs :: "'v twl_clause list" and
    C :: "'v twl_clause"
  defines "S \<equiv> rewatch_nat_cand_clss (lit_of L) M (Cs, Ks)"
  assumes
    wf: "\<forall>C \<in> set Cs. wf_twl_cls M C" and
    n_d: "no_dup (get_trail_of_cand Ks @ M)" and
    undef: "undefined_lit (get_trail_of_cand Ks @ M) (lit_of L)"
  shows
    "(\<forall>C \<in> set (fst S). wf_twl_cls (L # M) C) \<and>
     undefined_lit (get_trail_of_cand (snd S) @ M) (lit_of L) \<and>
     no_dup (get_trail_of_cand (snd S) @ M)" (is "?wf S \<and> ?undef S \<and> ?n_d S")
  using wf unfolding S_def
proof (induction Cs)
  case Nil note wf = this(1)
  show ?case
    using undef n_d by simp
next
  case (Cons C Cs) note IH = this(1) and wf = this(2)
  let ?S = "foldr (rewatch_nat_cand_single_clause (lit_of L) M) Cs ([], Ks)"
  let ?T = "rewatch_nat_cand_single_clause (lit_of L) M C ?S"
  have wf': "\<forall>a\<in>set Cs. wf_twl_cls M a" and wf_C: "wf_twl_cls M C"
    using wf by simp_all
  then have
    IH_wf: "\<forall>a\<in>set (fst ?S). wf_twl_cls (L # M) a" and
    IH_undef: "undefined_lit (get_trail_of_cand (snd ?S) @ M) (lit_of L)" and
    IH_nd: "no_dup (get_trail_of_cand (snd ?S) @ M)"
    using IH[OF wf'] unfolding rewatch_nat_cand_clss.simps by blast+
  have wf_C': "wf_twl_cls (L # M) (hd (fst (rewatch_nat_cand_single_clause (lit_of L) M C
    (fst ?S, snd ?S))))"
    using wf_rewatch_nat_cand_single_clause[of M C  "snd ?S" L "fst ?S"]
    using IH_wf IH_undef IH_nd wf by auto
  have "?wf ?T"
    using wf_C apply (cases rule: wf_rewatch_nat_cand_single_clause_cases[of M C "lit_of L"
     "fst ?S" "snd ?S"])
    using IH_wf wf_C' by (auto simp del: wf_twl_cls.simps)
  moreover have "?undef ?T"
    using wf_C apply (cases rule: wf_rewatch_nat_cand_single_clause_cases[of M C "lit_of L"
     "fst ?S" "snd ?S"])
    using IH_undef by (auto simp del: wf_twl_cls.simps simp:
       atm_of_eq_atm_of defined_lit_map
      image_Un uminus_lit_swap lits_of_def)
  moreover have "?n_d ?T"
    using wf_C apply (cases rule: wf_rewatch_nat_cand_single_clause_cases[of M C "lit_of L"
     "fst ?S" "snd ?S"])
    using IH_nd by (auto simp del: wf_twl_cls.simps simp: defined_lit_map image_Un image_image
      comp_def)
  ultimately show ?case by simp
qed
 *)

(*lemma
  fixes Ks :: "'v candidate" and M :: "('v, nat, 'v twl_clause) marked_lits" and
    L :: "('v, nat, 'v twl_clause) marked_lit" and Cs :: "'v twl_clause list" and
    C :: "'v twl_clause" and S :: "'v twl_state"
  defines "T \<equiv> rewatch_nat_cand (lit_of L) (TWL_State_Cand S Ks)"
  assumes
    wf: "wf_twl_state S" and
    n_d: "no_dup (get_trail_of_cand Ks @ raw_trail S)" and
    undef: "undefined_lit (get_trail_of_cand Ks @ raw_trail S) (lit_of L)"
  shows "wf_twl_state (raw_cons_trail L (twl_state T))"
proof -
  obtain U K' where
    U: "rewatch_nat_cand_clss (lit_of L) (raw_trail S) (raw_init_clss S, Ks) = (U, K')"
    (is "?H = _") by (cases ?H)

  obtain V K'' where
    V: "rewatch_nat_cand_clss (lit_of L) (raw_trail S) (raw_learned_clss S, K') = (V, K'')"
    (is "?H = _") by (cases ?H)
  have
    wf_U: "(\<forall>C\<in>set U. wf_twl_cls (L # raw_trail S) C)" and
    undef_K: "undefined_lit (get_trail_of_cand K' @ raw_trail S) (lit_of L)" and
    n_d_K: "no_dup (get_trail_of_cand K' @ raw_trail S)"
    using wf n_d wf_foldr_rewatch_nat_cand_single_clause[of "raw_init_clss S" "raw_trail S"
      Ks L] undef unfolding wf_twl_state_def by (simp_all add:
      CDCL_Two_Watched_Literals.twl.raw_clauses_def U)

  have wf_V: "(\<forall>C\<in>set V. wf_twl_cls (L # raw_trail S) C)"
    using wf undef_K n_d_K wf_foldr_rewatch_nat_cand_single_clause[of "raw_learned_clss S"
      "raw_trail S" K' L] unfolding wf_twl_state_def by (simp add:
      CDCL_Two_Watched_Literals.twl.raw_clauses_def U V)
  show ?thesis
    using undef n_d  wf_U wf_V unfolding T_def wf_twl_state_def by (auto simp: U V comp_def
    CDCL_Two_Watched_Literals.twl.raw_clauses_def defined_lit_map)
qed
 *)
end