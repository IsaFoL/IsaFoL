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

  The function returns a couple composed of a list of clauses and a candidate.

  TODO: check what is going on when the other literal is L.\<close>
fun
  rewatch_nat_cand_single_clause ::
  "'v literal \<Rightarrow> ('v, nat, 'v twl_clause) marked_lits \<Rightarrow> 'v twl_clause \<Rightarrow>
    'v twl_clause list \<times> 'v candidate \<Rightarrow>
     'v twl_clause list  \<times> 'v candidate"
where
"rewatch_nat_cand_single_clause L M C (Cs, Ks) =
  (if - L \<in> set (watched C) then
     case filter (\<lambda>L'. L' \<notin> set (watched C) \<and> - L' \<notin> insert L (lits_of_l M)) (unwatched C) of
       [] \<Rightarrow>
         (case remove1 (-L) (watched C) of (* contains at most a single element *)
             [] \<Rightarrow> (C # Cs, Prop_Or_Conf (prop_queue Ks)
               (find_earliest_conflict (prop_queue Ks @ M) (Some C) (conflict Ks)))
           | L' # _ \<Rightarrow>
             if undefined_lit (prop_queue Ks @ M) L' \<and> atm_of L \<noteq> atm_of L'
             then (C # Cs, Prop_Or_Conf (Propagated L' C # prop_queue Ks) (conflict Ks))
             else
               (if -L' \<in> lits_of_l (prop_queue Ks @ M)
               then (C # Cs, Prop_Or_Conf (prop_queue Ks)
                 (find_earliest_conflict (prop_queue Ks @ M) (Some C) (conflict Ks)))
               else (C # Cs, Ks)))
     | L' # _ \<Rightarrow>
       (TWL_Clause (L' # remove1 (-L) (watched C)) (-L # remove1 L' (unwatched C)) # Cs, Ks)
  else
    (C # Cs, Ks))"

declare rewatch_nat_cand_single_clause.simps[simp del]

lemma CNot_mset_replicate[simp]:
  "CNot (mset (replicate n (- L))) = (if n = 0 then {} else {{#L#}})"
  by (induction n) auto

lemma wf_rewatch_nat_cand_single_clause_cases[consumes 1, case_names wf lit_notin propagate conflict
  no_conflict update_cls]:
  assumes
    wf: "wf_twl_cls M C" and
    lit_notin: "-L \<notin> set (watched C) \<Longrightarrow>
      rewatch_nat_cand_single_clause L M C (Cs, Ks) = (C # Cs, Ks) \<Longrightarrow>
      P"
      and
    single_lit_watched: "-L \<in> set (watched C) \<Longrightarrow>
      filter (\<lambda>L'. L' \<notin> set (watched C) \<and> - L' \<notin> insert L (lits_of_l M)) (unwatched C) = [] \<Longrightarrow>
      watched C = [-L] \<Longrightarrow>
      set (unwatched C) \<subseteq> {-L} \<Longrightarrow>
      rewatch_nat_cand_single_clause L M C (Cs, Ks) = (C # Cs, Prop_Or_Conf (prop_queue Ks)
        (find_earliest_conflict (prop_queue Ks @ M) (Some C) (conflict Ks))) \<Longrightarrow>
      P"
      and
    propagate: "\<And>L'. -L \<in> set (watched C) \<Longrightarrow>
      filter (\<lambda>L'. L' \<notin> set (watched C) \<and> - L' \<notin> insert L (lits_of_l M)) (unwatched C) = [] \<Longrightarrow>
      set (watched C) = {-L, L'} \<Longrightarrow>
      undefined_lit (prop_queue Ks @ M) L' \<Longrightarrow>
      atm_of L \<noteq> atm_of L' \<Longrightarrow>
      rewatch_nat_cand_single_clause L M C (Cs, Ks) =
        (C # Cs, Prop_Or_Conf (Propagated L' C # prop_queue Ks) (conflict Ks)) \<Longrightarrow>
      P"
      and
    conflict: "\<And>L'. -L \<in> set (watched C) \<Longrightarrow>
      filter (\<lambda>L'. L' \<notin> set (watched C) \<and> - L' \<notin> insert L (lits_of_l M)) (unwatched C) = [] \<Longrightarrow>
      set (watched C) = {-L, L'} \<Longrightarrow>
      -L' \<in> insert L (lits_of_l (prop_queue Ks @ M)) \<Longrightarrow>
      rewatch_nat_cand_single_clause L M C (Cs, Ks) = (C # Cs, Prop_Or_Conf (prop_queue Ks)
        (find_earliest_conflict (prop_queue Ks @ M) (Some C) (conflict Ks))) \<Longrightarrow>
      P"
      and
    no_conflict: "\<And>L'. -L \<in> set (watched C) \<Longrightarrow>
      filter (\<lambda>L'. L' \<notin> set (watched C) \<and> - L' \<notin> insert L (lits_of_l M)) (unwatched C) = [] \<Longrightarrow>
      set (watched C) = {-L, L'} \<Longrightarrow>
      L' \<in> insert L (lits_of_l (prop_queue Ks @ M)) \<Longrightarrow>
      rewatch_nat_cand_single_clause L M C (Cs, Ks) = (C # Cs, Ks) \<Longrightarrow>
      P"
      and
    update_cls: "\<And>L' fUW. -L \<in> set (watched C) \<Longrightarrow>
      filter (\<lambda>L'. L' \<notin> set (watched C) \<and> - L' \<notin> insert L (lits_of_l M)) (unwatched C) = L' # fUW
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
        proof (cases "filter (\<lambda>L'. L' \<notin> set (watched C) \<and> - L' \<notin> insert L (lits_of_l M))
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
                apply (cases "undefined_lit (prop_queue Ks @ M) L'\<and> atm_of L \<noteq> atm_of L' ")
                apply (rule propagate)
                  using L filter C Cons dist
                  apply (auto simp: rewatch_nat_cand_single_clause.simps atm_of_eq_atm_of)[6]
                apply (cases "-L' \<in> insert L (lits_of_l (prop_queue Ks @ M))")
                apply (rule conflict)
                  using L filter C Cons apply (auto simp: rewatch_nat_cand_single_clause.simps)[5]
                  apply (rule no_conflict)
                  using L filter C Cons by (auto simp: rewatch_nat_cand_single_clause.simps
                    defined_lit_map lits_of_def image_Un atm_of_eq_atm_of)
            qed
        qed
    qed
qed

lemmas rewatch_nat_cand_single_clause_cases =
  wf_rewatch_nat_cand_single_clause_cases[OF wf_twl_cls_append[of "prop_queue _"], consumes 2,
    case_names wf lit_notin propagate conflict no_conflict update_cls]

lemma no_dup_rewatch_nat_cand_single_clause:
  fixes L :: "'v literal"
  assumes
    L: "L \<in> lits_of_l M" and
    wf: "wf_twl_cls (prop_queue Ks @ M) C" and
    n_d: "no_dup (prop_queue Ks @ M)"
  shows "no_dup (M @ prop_queue (snd (rewatch_nat_cand_single_clause L M C (Cs, Ks))))"
  using n_d wf apply (cases rule: rewatch_nat_cand_single_clause_cases[of Ks M C L Cs Ks])
  using L n_d by (auto simp: defined_lit_map)

lemma wf_twl_cls_prop_in_trailD:
  assumes "wf_twl_cls M (TWL_Clause W UW)"
  shows "\<forall>L \<in> set W. -L \<in> lits_of_l M \<longrightarrow> (\<forall>L' \<in> set UW. L' \<notin> set W \<longrightarrow> -L' \<in> lits_of_l M)"
  using assms by auto

lemma rewatch_nat_cand_single_clause_conflict:
  assumes
    L: "L \<in> lits_of_l M" and
    wf: "wf_twl_cls (prop_queue Ks @ M) C" and
    conf: "conflict Ks = Some D" and
    conf': "conflict (snd (rewatch_nat_cand_single_clause L M C (Cs, Ks))) = Some D'" and
    n_d: "no_dup (prop_queue Ks @ M)" and
    confI: "prop_queue Ks @ M \<Turnstile>as CNot (mset (raw_clause D))"
  shows "prop_queue Ks @ M \<Turnstile>as CNot (mset (raw_clause D'))"
  apply (cases C)
  using n_d wf apply (cases rule: rewatch_nat_cand_single_clause_cases[of Ks M C L Cs Ks])
  prefer 4
    using conf conf' confI L find_earliest_conflict_cases[of "prop_queue Ks @ M" C D] wf
    apply (fastforce simp add: raw_clause_def true_annots_true_cls_def_iff_negation_in_model
        simp del: watched_decided_most_recently.simps wf_twl_cls.simps
        dest!: wf_twl_cls_prop_in_trailD)[]
  using conf conf' confI L find_earliest_conflict_cases[of "prop_queue Ks @ M" C D]
  apply (auto simp add: raw_clause_def  true_annots_true_cls_def_iff_negation_in_model
      simp del: watched_decided_most_recently.simps
    )[5]
  done

lemma rewatch_nat_cand_single_clause_conflict_found:
  assumes
    L: "L \<in> lits_of_l M" and
    wf: "wf_twl_cls (prop_queue Ks @ M) C" and
    n_d: "no_dup (prop_queue Ks @ M)" and
    conf: "conflict Ks = None" and
    conf': "conflict (snd (rewatch_nat_cand_single_clause L M C (Cs, Ks))) = Some D'"
  shows "prop_queue Ks @ M \<Turnstile>as CNot (mset (raw_clause D'))"
  apply (cases C)
  using n_d wf apply (cases rule: rewatch_nat_cand_single_clause_cases[of Ks M C L Cs Ks])
  using conf conf' L
  by (auto simp add: raw_clause_def filter_empty_conv true_annots_true_cls_def_iff_negation_in_model
     simp del: watched_decided_most_recently.simps)

lemma rewatch_nat_cand_single_clause_clauses:
  assumes
    wf: "wf_twl_cls (prop_queue Ks @ M) C" and
    n_d: "no_dup (prop_queue Ks @ M)"
  shows "clauses_of_l (map raw_clause (fst (rewatch_nat_cand_single_clause L M C (Cs, Ks)))) =
      clauses_of_l (map raw_clause (C # Cs))"
  apply (cases C)
  using n_d wf apply (cases rule: rewatch_nat_cand_single_clause_cases[of Ks M C L Cs Ks])
  apply (auto simp: raw_clause_def filter_empty_conv true_annots_true_cls_def_iff_negation_in_model
     simp del: watched_decided_most_recently.simps)
  apply (auto dest:filter_in_list_prop_verifiedD simp: multiset_eq_iff)
  done

text \<open>This lemma is \<^emph>\<open>wrong\<close>: we are speaking of half-update data-structure, meaning that
  @{term "wf_twl_cls (prop_queue Ks @ M) C"} is the wrong assumption to use.\<close>
lemma
  fixes Ks :: "'v candidate" and M :: "('v, nat, 'v twl_clause) marked_lit list"
  and L :: "'v literal" and Cs :: "'v twl_clause list" and C :: "'v twl_clause"
  defines "S \<equiv> rewatch_nat_cand_single_clause L M C (Cs, Ks)"
  assumes wf: "wf_twl_cls (prop_queue Ks @ M) C" and
    n_d: "no_dup (prop_queue Ks @ M)"
  shows "wf_twl_cls (prop_queue (snd S) @ M) C"
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
          simp del: watched_decided_most_recently.simps)
         done
    next
      case t: wf
      then show ?thesis
        using wf unfolding S_def by simp
    qed
qed

lemma wf_rewatch_nat_cand_single_clause:
  fixes Ks :: "'v candidate" and M :: "('v, nat, 'v twl_clause) marked_lit list" and
    L :: "('v, nat, 'v twl_clause) marked_lit" and Cs :: "'v twl_clause list" and
    C :: "'v twl_clause"
  defines "S \<equiv> rewatch_nat_cand_single_clause (lit_of L) M C (Cs, Ks)"
  assumes
    wf: "wf_twl_cls M C" and
    n_d: "no_dup (prop_queue Ks @ M)" and
    undef: "undefined_lit (prop_queue Ks @ M) (lit_of L)"
  shows "wf_twl_cls (L # M) (hd (fst S))"
proof -
  obtain W UW where C: "C = TWL_Clause W UW"
    by (cases C)
  have t: "watched_decided_most_recently M (TWL_Clause W UW)" and
    wf': "distinct W \<and> length W \<le> 2 \<and> (length W < 2 \<longrightarrow> set UW \<subseteq> set W)" and
    H: "\<forall>L \<in> set W. -L \<in> lits_of_l M \<longrightarrow> (\<forall>L' \<in> set UW. L' \<notin> set W \<longrightarrow> -L' \<in> lits_of_l M)"
    using wf C by auto
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

lemma rewatch_nat_cand_single_clause_no_dup:
  fixes Ks :: "'v candidate" and M :: "('v, nat, 'v twl_clause) marked_lit list"
  and L :: "'v literal" and Cs :: "'v twl_clause list" and C :: "'v twl_clause"
  defines "S \<equiv> rewatch_nat_cand_single_clause L M C (Cs, Ks)"
  assumes wf: "wf_twl_cls M C" and
    n_d: "no_dup (prop_queue Ks @ M)" and
    undef: "undefined_lit (prop_queue Ks @ M) L"
  shows "no_dup (prop_queue (snd S) @ M)"
  using wf n_d  apply (cases rule: wf_rewatch_nat_cand_single_clause_cases[of M C L Cs Ks])
  using undef unfolding S_def by (simp_all add: defined_lit_map image_Un)


fun
  rewatch_nat_cand_clss ::
  "'v literal \<Rightarrow> ('v, nat, 'v twl_clause) marked_lits \<Rightarrow>
    'v twl_clause list \<times> 'v candidate \<Rightarrow>
     'v twl_clause list  \<times> 'v candidate"
where
"rewatch_nat_cand_clss L M (Cs, Ks) =
  foldr (rewatch_nat_cand_single_clause L M) Cs ([], Ks)"

fun rewatch_nat_cand :: "'a literal \<Rightarrow> 'a twl_state_cands \<Rightarrow> 'a twl_state_cands"  where
"rewatch_nat_cand L (TWL_State_Cand S Ks) =
  (let
    (N, K) = rewatch_nat_cand_clss L (raw_trail S) (raw_init_clss S, Ks);
    (U, K') = rewatch_nat_cand_clss L (raw_trail S) (raw_learned_clss S, K) in
  TWL_State_Cand
    (TWL_State (raw_trail S) N U (backtrack_lvl S) (raw_conflicting S))
    K')"

lemma wf_foldr_rewatch_nat_cand_single_clause:
  fixes Ks :: "'v candidate" and M :: "('v, nat, 'v twl_clause) marked_lits" and
    L :: "('v, nat, 'v twl_clause) marked_lit" and Cs :: "'v twl_clause list" and
    C :: "'v twl_clause"
  defines "S \<equiv> foldr (rewatch_nat_cand_single_clause (lit_of L) M) Cs ([], Ks)"
  assumes
    wf: "\<forall>C \<in> set Cs. wf_twl_cls M C" and
    n_d: "no_dup (prop_queue Ks @ M)" and
    undef: "undefined_lit (prop_queue Ks @ M) (lit_of L)"
  shows
    "(\<forall>C \<in> set (fst S). wf_twl_cls (L # M) C) \<and>
     undefined_lit (prop_queue (snd S) @ M) (lit_of L) \<and>
     no_dup (prop_queue (snd S) @ M)" (is "?wf S \<and> ?undef S \<and> ?n_d S")
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
    IH_undef: "undefined_lit (prop_queue (snd ?S) @ M) (lit_of L)" and
    IH_nd: "no_dup (prop_queue (snd ?S) @ M)"
    using IH[OF wf'] by blast+
  have wf_C': "wf_twl_cls (L # M) (hd (fst (rewatch_nat_cand_single_clause (lit_of L) M C
    (fst ?S, snd ?S))))"
    using wf_rewatch_nat_cand_single_clause[of M C  "snd ?S" L "fst ?S"]
    using IH_wf IH_undef IH_nd wf by simp
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
    using IH_nd by (auto simp del: wf_twl_cls.simps simp: defined_lit_map)
  ultimately show ?case by simp
qed

end