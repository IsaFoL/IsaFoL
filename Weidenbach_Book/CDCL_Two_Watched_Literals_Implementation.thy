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
  the propagation \<^emph>\<open>before\<close> the invariants holds again.

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
  @{typ "('v, nat, 'v twl_clause) ann_lits"} with only @{term Propagated}. However, we do not
  want to define the function for @{term Decided} too. The following function makes the conversion
  from the pair to the trail:
  \<close>
abbreviation get_trail_of_cand where
"get_trail_of_cand C \<equiv> map (case_prod Propagated) (prop_queue C)"

datatype 'v twl_state_cands =
  TWL_State_Cand (twl_state: "'v twl_state")
    (cand: "'v candidate")

fun raw_cons_trail where
"raw_cons_trail L (TWL_State M N U k C) = TWL_State (L # M) N U k C"

lemma raw_init_clss_raw_cons_trail[simp]:
  "raw_init_clss (raw_cons_trail L T) = raw_init_clss T"
  by (cases T) auto

lemma raw_learned_clss_raw_cons_trail[simp]:
  "raw_learned_clss (raw_cons_trail L T) = raw_learned_clss T"
  by (cases T) auto

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

fun find_earliest_conflict :: "('v, nat, 'v twl_clause) ann_lits \<Rightarrow>
  'v twl_clause option \<Rightarrow> 'v twl_clause option \<Rightarrow> 'v twl_clause option" where
"find_earliest_conflict _ None C = C" |
"find_earliest_conflict _ C None = C" |
"find_earliest_conflict [] C _ = C" |
"find_earliest_conflict (L # M) (Some C) (Some D) =
  (case (M \<Turnstile>a clause C, \<not>M\<Turnstile>a clause D) of
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
  conflict candidate.\<close>
text \<open>We make the function slightly more general than needed:
  \<^item> @{term removeAll} could be replace by @{term remove1}, since there are no duplicates in
  well-founded two-watched literals.
  \<^item> we match @{term "removeAll (-L) (watched C)"} with respect to @{term "L' # Ls'"}, while
  @{term "[L']"} is enough.\<close>
text \<open>The function returns a couple composed of a list of clauses and a candidate.\<close>
fun
  rewatch_nat_cand_single_clause ::
  "'v literal \<Rightarrow> ('v, nat, 'v twl_clause) ann_lits \<Rightarrow> 'v twl_clause \<Rightarrow>
    'v twl_clause list \<times> 'v candidate \<Rightarrow>
     'v twl_clause list  \<times> 'v candidate"
where
"rewatch_nat_cand_single_clause L M C (Cs, Ks) =
  (if - L \<in> set (watched C) then
     case filter (\<lambda>L'. L' \<notin> set (watched C) \<and>
       - L' \<notin> insert L (lits_of_l (M @ get_trail_of_cand Ks))) (unwatched C) of
       [] \<Rightarrow>
         (case removeAll (-L) (watched C) of (* contains at most a single element *)
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

text \<open>We do no check if the structural invariants about the 2-WL clauses holds. Otherwise,
  @{term "raw_trail U @ get_trail_of_cand (Prop_Or_Conf Q D) \<Turnstile>a clause C"} would work to and
  would be a better definition.\<close>
fun \<mu>TWL where
"\<mu>TWL (TWL_State_Cand U K) =
  card {L \<in> atms_of_mm (twl.clauses U). L \<notin> atm_of ` lits_of_l (raw_trail U @ get_trail_of_cand K)}"

lemma get_all_mark_of_propagated_get_trail_cond[simp]:
  "get_all_mark_of_propagated (get_trail_of_cand K) = map snd (prop_queue K)"
proof -
  obtain Q D where K: "K = Prop_Or_Conf Q D" by (cases K)
  show ?thesis unfolding K by (induction Q) auto
qed

fun rewatch_nat_cand_clss ::
  "'v literal \<Rightarrow> ('v, nat, 'v twl_clause) ann_lits \<Rightarrow>
    'v twl_clause list \<times> 'v candidate \<Rightarrow>
     'v twl_clause list  \<times> 'v candidate"
where
"rewatch_nat_cand_clss L M (Cs, Ks) =
  foldr (rewatch_nat_cand_single_clause L M) Cs ([], Ks)"

declare rewatch_nat_cand_clss.simps[simp del]

lemma struct_wf_rewatch_nat_cand_single_clause_cases[consumes 1, case_names wf lit_notin propagate
  conflict no_conflict update_cls]:
  assumes
    wf: "struct_wf_twl_cls C" and
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
            apply - by (rule update_cls) (auto simp add: rewatch_nat_cand_single_clause.simps L)
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
              have [simp]: "\<And>L'. removeAll L' (watched C) = remove1 L' (watched C)"
                using dist by (simp add: distinct_remove1_removeAll)
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

lemma wf_twl_cls_struct_wf_twl_cls: "wf_twl_cls M C \<Longrightarrow> struct_wf_twl_cls C"
  by (cases C) auto

lemmas wf_rewatch_nat_cand_single_clause_cases =
  struct_wf_rewatch_nat_cand_single_clause_cases[OF wf_twl_cls_struct_wf_twl_cls]

lemma prop_queue_rewatch_nat_cand_single_clause_eq_or_cons:
  "prop_queue (snd (rewatch_nat_cand_single_clause L M C S)) = prop_queue (snd S) \<or>
  (\<exists>L'. prop_queue (snd (rewatch_nat_cand_single_clause L M C S)) = L' # prop_queue (snd S))"
  apply (cases C, cases S)
  apply (auto simp: raw_clause_def filter_empty_conv true_annots_true_cls_def_iff_negation_in_model
    comp_def rewatch_nat_cand_single_clause.simps lits_of_def image_image split: list.splits
     simp del: watched_decided_most_recently.simps)
  done

lemma lit_of_case_Propagated[simp]: "lit_of (case x of (x, xa) \<Rightarrow> Propagated x xa) = fst x"
  by (cases x) auto

lemma prop_queue_first_is_undefined:
  assumes "prop_queue (snd (rewatch_nat_cand_single_clause L M C S)) = L' # prop_queue (snd S)"
  shows
    "undefined_lit (get_trail_of_cand (snd S) @ M) (fst L')" and
    "snd L' = C" and
    "fst L' \<in># clause C" and
    "fst L' \<noteq> -L" and
    "fst L' \<noteq> L"
        using assms
          apply (cases C, cases S)
          apply (auto simp: rewatch_nat_cand_single_clause.simps
            split: list.splits if_splits
            simp del: watched_decided_most_recently.simps)
        using assms
        apply (cases C, cases S)
        apply (auto simp: rewatch_nat_cand_single_clause.simps
          split: list.splits if_splits
          simp del: watched_decided_most_recently.simps)
      using assms
      apply (cases C, cases S)
      apply (auto simp: rewatch_nat_cand_single_clause.simps clause_def raw_clause_def
        split: list.splits if_splits
        simp del: watched_decided_most_recently.simps
        dest!: arg_cong[of "removeAll _ _" _ set])
      using assms
    apply (cases C, cases S)
    apply (auto simp: rewatch_nat_cand_single_clause.simps clause_def raw_clause_def
      split: list.splits if_splits
      simp del: watched_decided_most_recently.simps
      dest!: arg_cong[of "removeAll _ _" _ set])
    using assms
  apply (cases C, cases S)
  apply (auto simp: rewatch_nat_cand_single_clause.simps clause_def raw_clause_def
    split: list.splits if_splits
    simp del: watched_decided_most_recently.simps
    dest!: arg_cong[of "removeAll _ _" _ set])
  done

lemmas rewatch_nat_cand_single_clause_cases =
  wf_rewatch_nat_cand_single_clause_cases[OF wf_twl_cls_append[of "get_trail_of_cand _"],
    consumes 2, case_names wf lit_notin propagate conflict no_conflict update_cls]

fun rewatch_nat_cand :: "'a literal \<Rightarrow> 'a twl_state_cands \<Rightarrow> 'a twl_state_cands"  where
"rewatch_nat_cand L (TWL_State_Cand S Ks) =
  (let
    (N, K) = rewatch_nat_cand_clss L (raw_trail S) (raw_init_clss S, Ks);
    (U, K') = rewatch_nat_cand_clss L (raw_trail S) (raw_learned_clss S, K) in
  TWL_State_Cand
    (TWL_State (raw_trail S) N U (backtrack_lvl S) (raw_conflicting S))
    K')"

lemma rewatch_nat_cand_single_clause_hd:
  "raw_clss_l (fst (rewatch_nat_cand_single_clause L M C K)) =
      raw_clss_l ((C # (fst K)))"
  apply (cases C, cases K)
  apply (auto simp: raw_clause_def filter_empty_conv true_annots_true_cls_def_iff_negation_in_model
    comp_def rewatch_nat_cand_single_clause.simps lits_of_def image_image
    clause_def
    split: list.splits
     simp del: watched_decided_most_recently.simps)
  apply (auto dest: filter_in_list_prop_verifiedD simp: multiset_eq_iff)
  done

lemma rewatch_nat_cand_single_clause_clauses:
  "raw_clss_l (fst (rewatch_nat_cand_clss L M (N, Ks))) = raw_clss_l N"
  by (induction N) (simp_all add: rewatch_nat_cand_clss.simps
    rewatch_nat_cand_single_clause_hd[simplified])

fun undefined_lit_list :: "('a literal \<times> 'a twl_clause) list
   \<Rightarrow> ('a, 'b, 'a twl_clause) ann_lit list \<Rightarrow> bool" where
"undefined_lit_list [] _ \<longleftrightarrow> True" |
"undefined_lit_list (L # Ls) M \<longleftrightarrow> undefined_lit (map (case_prod Propagated) Ls @ M) (fst L) \<and>
  undefined_lit_list Ls M"

lemma undefined_lit_list_append[simp]:
  "undefined_lit_list (Ls @ Ls') M \<longleftrightarrow>
    undefined_lit_list Ls (map (case_prod Propagated) Ls' @ M) \<and>
    undefined_lit_list Ls' M"
  by (induction Ls) auto

lemma prop_queue_rewatch_nat_cand_clss_eq_or_cons:
  "\<exists>L'. prop_queue (snd (rewatch_nat_cand_clss L M K)) = L' @ prop_queue (snd K)
  \<and> undefined_lit_list L' (get_trail_of_cand (snd K) @ M)
  \<and> (\<forall>(l, C) \<in> set L'. C \<in> set (fst K) \<and> l \<in># clause C \<and> l \<noteq> -L \<and> l \<noteq> L)" (is "\<exists>L'. ?P K L'")
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
      then obtain L' where
        L': "prop_queue (snd (rewatch_nat_cand_clss L M (Cs, Q))) = L' @ prop_queue (snd (Cs, Q))" and
        undef: "undefined_lit_list L' (get_trail_of_cand (snd (Cs, Q)) @ M)" and
        aL': "\<forall>a\<in>set L'. case a of (l, C) \<Rightarrow> C \<in> set (fst (Cs, Q)) \<and> l \<in># clause C \<and> l \<noteq> -L \<and>
          l \<noteq> L"
        by fast
      consider
          (Nil) "prop_queue (snd (rewatch_nat_cand_single_clause L M C
             (foldr (rewatch_nat_cand_single_clause L M) Cs ([], Q)))) =
           prop_queue (snd (foldr (rewatch_nat_cand_single_clause L M) Cs ([], Q)))"
        | (Cons) L'' where
          "prop_queue (snd (rewatch_nat_cand_single_clause L M C
             (foldr (rewatch_nat_cand_single_clause L M) Cs ([], Q)))) =
           L'' # prop_queue (snd (foldr (rewatch_nat_cand_single_clause L M) Cs ([], Q)))"
        using prop_queue_rewatch_nat_cand_single_clause_eq_or_cons[of L M C
         "foldr (rewatch_nat_cand_single_clause L M) Cs ([], Q)"] by blast
    then show ?case
      proof cases
        case Nil
        then show ?thesis
          using L' undef aL' by (auto simp: rewatch_nat_cand_clss.simps)[]
      next
        case (Cons L'')
        then show ?thesis
          using L' undef aL'  prop_queue_first_is_undefined[of L M C
           "foldr (rewatch_nat_cand_single_clause L M) Cs ([], Q)" L'']
          by (auto simp: rewatch_nat_cand_clss.simps)
      qed
    qed
qed

lemma prop_queue_rewatch_nat_cand_eq_or_cons:
  "\<exists>L'. prop_queue (cand (rewatch_nat_cand L S)) = L' @ prop_queue (cand S)
  \<and> undefined_lit_list L' (get_trail_of_cand (cand S) @ raw_trail (twl_state S))
  \<and> (\<forall>(l, C) \<in> set L'. C \<in> set (twl.raw_clauses (twl_state S)) \<and> l \<in># clause C
    \<and> l \<noteq> -L \<and> l \<noteq> L)"
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

lemma twl_clauses_rewatch_nat_cand[simp]:
  "twl.clauses (twl_state (rewatch_nat_cand L S)) = twl.clauses (twl_state S)"
proof -
  obtain T Ks where S: "S = TWL_State_Cand T Ks"
    by (cases S)
  obtain U K' where
    U: "rewatch_nat_cand_clss L (raw_trail T) (raw_init_clss T, Ks) = (U, K')"
    (is "?H = _") by (cases ?H)

  obtain V K'' where
    V: "rewatch_nat_cand_clss L (raw_trail T) (raw_learned_clss T, K') = (V, K'')"
    (is "?H = _") by (cases ?H)

  have "mset (map clause U) = mset (map clause (raw_init_clss T))"
    using rewatch_nat_cand_single_clause_clauses[of L "raw_trail T" "raw_init_clss T"
      "Ks"] by (auto simp: comp_def U clause_def raw_clause_def clause_def_lambda)
  moreover have "mset (map clause V) = mset (map clause
  (raw_learned_clss T))"
    using rewatch_nat_cand_single_clause_clauses[of L "raw_trail T" "raw_learned_clss T"
      "K'"] by (auto simp: comp_def V clause_def_lambda raw_clause_def)
  ultimately show ?thesis  unfolding S
    by (auto simp: comp_def twl.raw_clauses_def U V clause_def raw_clause_def)
qed

lemma true_annot_mono_append_append:
  "A @ C \<Turnstile>a D \<Longrightarrow> A @ B @ C \<Turnstile>a D"
  "A @ C \<Turnstile>a D \<Longrightarrow> L # A @ B @ C \<Turnstile>a D"
  by (rule true_annot_mono; auto)+

lemma true_annot_mono':
  "\<not>I' \<Turnstile>a N \<Longrightarrow> I \<Turnstile>a N \<Longrightarrow> \<not>set I \<subseteq> set I' "
  using true_annot_mono by blast

lemma prop_queue_cand_raw_cons_trail[simp]:
  "prop_queue (cand (raw_cons_trail_pq (Propagated L C') S)) = prop_queue (cand S)"
  by (cases S) auto

lemma \<mu>TWL_Prop_Or_Conf_append_raw_cons_trail:
  "\<mu>TWL (TWL_State_Cand S (Prop_Or_Conf (l @ [(L, C')]) D)) =
    \<mu>TWL (TWL_State_Cand (raw_cons_trail (Propagated L C') S) (Prop_Or_Conf l D))"
  by (auto simp: comp_def)

lemma get_all_mark_of_propagated_map_Propagated[simp]:
  "get_all_mark_of_propagated (map (\<lambda>(x, y). Propagated x y) Q) = map snd Q"
  by (induction Q) auto

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

  have H1: "set_mset (mset (map clause U)) =
    clause ` set_mset (mset (raw_init_clss S))"
    using rewatch_nat_cand_single_clause_clauses[of L "raw_trail S" "raw_init_clss S"
      "Prop_Or_Conf Q D"] by (auto simp: comp_def U clause_def_lambda)
  moreover
    have H2: "set_mset (mset (map clause V)) =
      clause ` set_mset (mset (raw_learned_clss S))"
      using rewatch_nat_cand_single_clause_clauses[of L "raw_trail S" "raw_learned_clss S"
        "K'"] by (auto simp: comp_def V clause_def_lambda)
  show ?thesis
    using H1 H2
    by (auto simp: comp_def U V K'' twl.raw_clauses_def image_Un P (* raw_clause_def *)
      clause_def image_image lits_of_def intro!: Nat.diff_le_mono2 card_mono)
qed

text \<open>This purely technical lemma states that if there is no new defined literals, then @{term Ls}
  is empty.\<close>
lemma \<mu>TWL_eq_no_new_propagated_lit:
  assumes
    c: "card {La \<in> atms_of_ms (clause ` set (twl.raw_clauses S)).
      La \<noteq> atm_of L \<and> La \<notin> (\<lambda>x. atm_of (lit_of x)) ` set (raw_trail S) \<and>
      La \<notin> (\<lambda>x. atm_of (fst x)) ` set Ls \<and>
      La \<notin> (\<lambda>x. atm_of (fst x)) ` set l} =
    card {La \<in> atms_of_ms (clause ` set (twl.raw_clauses S)).
      La \<noteq> atm_of L \<and> La \<notin> (\<lambda>x. atm_of (lit_of x)) ` set (raw_trail S) \<and>
      La \<notin> (\<lambda>x. atm_of (fst x)) ` set l}" and
    undef: "undefined_lit_list Ls (map (\<lambda>(x, y). Propagated x y) l @ raw_trail S)" and
    C: "\<forall>(l, C)\<in>set Ls. C \<in> set (twl.raw_clauses S) \<and> l \<in># clause C \<and> l \<noteq> - L \<and> l \<noteq> L"
  shows "Ls = []"
proof (rule ccontr)
  assume "Ls \<noteq> []"
  then obtain L' C' Ls' where Ls: "Ls = (L', C') # Ls'"
    by (cases Ls) auto
  let ?D =" {La \<in> atms_of_ms (clause ` set (twl.raw_clauses S)).
      La \<noteq> atm_of L \<and> La \<notin> (\<lambda>x. atm_of (lit_of x)) ` set (raw_trail S) \<and>
      La \<notin> (\<lambda>x. atm_of (fst x)) ` set Ls \<and>
      La \<notin> (\<lambda>x. atm_of (fst x)) ` set l}"
  let ?C = " {La \<in> atms_of_ms (clause ` set (twl.raw_clauses S)).
      La \<noteq> atm_of L \<and> La \<notin> (\<lambda>x. atm_of (lit_of x)) ` set (raw_trail S) \<and>
      La \<notin> (\<lambda>x. atm_of (fst x)) ` set l}"
  have "?D \<subseteq> ?C"
    by blast
  moreover have "finite ?D"
    by auto
  ultimately have "?D = ?C"
    by (simp add: c card_subset_eq)
  then have H: "\<And>La. La \<in> atms_of_ms (clause ` set (twl.raw_clauses S)) \<Longrightarrow>
    La \<noteq> atm_of L \<Longrightarrow> La \<notin> (\<lambda>x. atm_of (lit_of x)) ` set (raw_trail S) \<Longrightarrow>
    La \<notin> (\<lambda>x. atm_of (fst x)) ` set l \<Longrightarrow>
    La \<notin> (\<lambda>x. atm_of (fst x)) ` set Ls"
    by blast
  have undef: "undefined_lit
    (map (\<lambda>(x, y). Propagated x y) Ls' @ map (\<lambda>(x, y). Propagated x y) l @ raw_trail S) L'"
    using undef unfolding Ls by auto
  have C': "C' \<in> set (twl.raw_clauses S)" and "L' \<in># clause C'" and LL': "L' \<noteq> -L" "L' \<noteq> L"
    using C unfolding Ls by auto
  then have "atm_of L' \<in> atms_of_ms (clause ` set (twl.raw_clauses S))"
    by (simp add: C' in_implies_atm_of_on_atms_of_ms)
  moreover have "atm_of L' \<noteq> atm_of L"
    using LL' by (auto simp: atm_of_eq_atm_of)
  moreover have "atm_of L' \<notin> (\<lambda>x. atm_of (lit_of x)) ` set (raw_trail S)" and
    "atm_of L' \<notin> (\<lambda>x. atm_of (fst x)) ` set l"
    using undef by (auto simp: defined_lit_map image_Un image_image)
  moreover have "atm_of L' \<in> (\<lambda>x. atm_of (fst x)) ` set Ls"
    unfolding Ls by auto
  ultimately show False using H[of "atm_of L'"] by fast
qed

text \<open>Implementation-wise, @{term "trail S \<Turnstile>as CNot (clause D)"} should be equivalent
  to there is no more propagation to do.\<close>
function do_propagate_or_conflict_step :: "'a twl_state_cands \<Rightarrow> 'a twl_state_cands" where
"do_propagate_or_conflict_step (TWL_State_Cand S (Prop_Or_Conf [] (Some D))) =
  (if trail S \<Turnstile>as CNot (clause D)
  then (update_conflicting_pq (Some (raw_clause D)) (TWL_State_Cand S (Prop_Or_Conf [] None)))
  else TWL_State_Cand S (Prop_Or_Conf [] (Some D)))" |
"do_propagate_or_conflict_step (TWL_State_Cand S (Prop_Or_Conf [] None)) =
  TWL_State_Cand S (Prop_Or_Conf [] None)" |
"do_propagate_or_conflict_step (TWL_State_Cand S (Prop_Or_Conf (l @ [(L, C')]) (Some D))) =
  (if trail S \<Turnstile>as CNot (clause D)
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
  obtain T Q' where T: "rewatch_nat_cand L (TWL_State_Cand S (Prop_Or_Conf l (Some D))) =
    TWL_State_Cand T Q'"
    by (cases "rewatch_nat_cand L (TWL_State_Cand S (Prop_Or_Conf l (Some D)))")
  have ST: "clause ` set (twl.raw_clauses T) =
    clause ` set (twl.raw_clauses S)"
    using twl_clauses_rewatch_nat_cand[of L "TWL_State_Cand S (Prop_Or_Conf l (Some D))"]
    unfolding T
    (* TODO tune proof *)
    apply (auto simp: comp_def twl.raw_clauses_def image_Un
          simp del: rewatch_nat_cand.simps)
    apply (metis (no_types, lifting) Un_iff image_eqI set_append set_map set_mset_mset union_code)+
    done
  have [simp]: "raw_trail T = raw_trail S"
    using T by (auto split: Product_Type.prod.splits)
  show ?case
    using YYY[of L C' S l "Some D"]
    prop_queue_rewatch_nat_cand_eq_or_cons[of L "TWL_State_Cand S (Prop_Or_Conf l (Some D))"]
    apply (auto simp add: comp_def lexn_n \<mu>TWL_Prop_Or_Conf_append_raw_cons_trail
      T ST \<mu>TWL_eq_no_new_propagated_lit[of S]
      simp del: lexn.simps(2) rewatch_nat_cand.simps
      simp add: lits_of_def image_image image_Un)
    done
next
  case (3 S l L C')
  obtain T Q' where T: "rewatch_nat_cand L (TWL_State_Cand S (Prop_Or_Conf l None)) =
    TWL_State_Cand T Q'"
    by (cases "rewatch_nat_cand L (TWL_State_Cand S (Prop_Or_Conf l None))")
  have ST: "clause ` set (twl.raw_clauses T) =
    clause ` set (twl.raw_clauses S)"
    using twl_clauses_rewatch_nat_cand[of L "TWL_State_Cand S (Prop_Or_Conf l None)"]
    unfolding T
    (* TODO tune proof *)
    apply (auto simp: comp_def twl.raw_clauses_def image_Un
          simp del: rewatch_nat_cand.simps)
    apply (metis (no_types, lifting) Un_iff image_eqI set_append set_map set_mset_mset union_code)+
    done
  have [simp]: "raw_trail T = raw_trail S"
    using T by (auto split: Product_Type.prod.splits)
  show ?case
    using YYY[of L C' S l None]
    prop_queue_rewatch_nat_cand_eq_or_cons[of L "TWL_State_Cand S (Prop_Or_Conf l None)"]
    apply (auto simp add: comp_def lexn_n \<mu>TWL_Prop_Or_Conf_append_raw_cons_trail
      T ST \<mu>TWL_eq_no_new_propagated_lit[of S]
      simp del: lexn.simps(2) rewatch_nat_cand.simps
      simp add: lits_of_def image_image image_Un)
    done
qed

lemma no_dup_rewatch_nat_cand_single_clause:
  fixes L :: "'v literal"
  assumes
    L: "L \<in> lits_of_l M" and
    wf: "wf_twl_cls (get_trail_of_cand Ks @ M) C" and
    n_d: "no_dup (get_trail_of_cand Ks @ M)"
  shows "no_dup (M @ get_trail_of_cand (snd (rewatch_nat_cand_single_clause L M C (Cs, Ks))))"
  using n_d wf apply (cases rule: rewatch_nat_cand_single_clause_cases[of Ks M C L M Cs Ks])
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
    confI: "get_trail_of_cand Ks @ M \<Turnstile>as CNot (clause D)"
  shows "get_trail_of_cand Ks @ M \<Turnstile>as CNot (clause D')"
  apply (cases C)
  using n_d wf apply (cases rule: rewatch_nat_cand_single_clause_cases[of Ks M C L M Cs Ks])
  prefer 4
    using conf conf' confI L
    apply (auto simp add: raw_clause_def true_annots_true_cls_def_iff_negation_in_model
      lits_of_def image_image image_Un Quickcheck_Exhaustive.orelse_def
        simp del: watched_decided_most_recently.simps wf_twl_cls.simps
        dest!: wf_twl_cls_prop_in_trailD)[]
  using conf conf' confI L find_earliest_conflict_cases[of "get_trail_of_cand Ks @ M" C D]
  apply (auto simp add: raw_clause_def  true_annots_true_cls_def_iff_negation_in_model
    Quickcheck_Exhaustive.orelse_def
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
  shows "get_trail_of_cand Ks @ M \<Turnstile>as CNot (clause D')"
  apply (cases C)
  using n_d wf apply (cases rule: rewatch_nat_cand_single_clause_cases[of Ks M C L M Cs Ks])
  using conf conf' L
  (* TODO tune proof *)
  apply (auto simp add: raw_clause_def filter_empty_conv true_annots_true_cls_def_iff_negation_in_model
    Quickcheck_Exhaustive.orelse_def lits_of_def image_image image_Un clause_def
     simp del: watched_decided_most_recently.simps)
  apply force+
  done

lemma rewatch_nat_cand_single_clause_no_dup:
  fixes Ks :: "'v candidate" and M :: "('v, nat, 'v twl_clause) ann_lit list"
  and L :: "'v literal" and Cs :: "'v twl_clause list" and C :: "'v twl_clause"
  defines "S \<equiv> rewatch_nat_cand_single_clause L M C (Cs, Ks)"
  assumes wf: "wf_twl_cls M C" and
    n_d: "no_dup (get_trail_of_cand Ks @ M)" and
    undef: "undefined_lit (get_trail_of_cand Ks @ M) L"
  shows "no_dup (get_trail_of_cand (snd S) @ M)"
  using wf n_d apply (cases rule: wf_rewatch_nat_cand_single_clause_cases[of M C L M Cs Ks])
  using undef unfolding S_def by (auto simp add: defined_lit_map image_Un image_image comp_def)

end