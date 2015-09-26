theory CDCL_Implementation
imports Propo_CDCL Propo_CDCL_Termination (*"~~/src/HOL/Library/Code_Target_Numeral"*)
begin

(*
code_pred cdcl_o .
values [mode: i \<Rightarrow> o] "{S. cdcl_o ([], {{#Pos (1::nat), Pos 2#}, {#Neg 1, Neg 2#}}, {}, 0, C_True) S}"
*)
(*TODO Move*)
declare Multiset.in_multiset_in_set[simp]

lemma remdups_mset_singleton_sum[simp]:
  "remdups_mset (A+{#a#}) = (if a \<in># A then remdups_mset A else {#a#} + remdups_mset A)"
  unfolding remdups_mset_def by (simp add: insert_absorb)

lemma mset_remdups_remdups_mset[simp]:
  "mset (remdups D) = remdups_mset (mset D)"
  by (induction D) (auto simp add: add.commute)

lemma distinct_mset_distinct[simp]:
  "distinct_mset (mset x) = distinct x"
  unfolding distinct_mset_def by (induction x) auto

lemma distinct_mset_set_distinct:
  "distinct_mset_set (mset ` set Cs) \<longleftrightarrow> (\<forall>c\<in> set Cs. distinct c)"
  unfolding distinct_mset_set_def by auto

lemma true_clss_remdups[simp]:
  "I \<Turnstile>s (mset \<circ> remdups) ` N \<longleftrightarrow>  I \<Turnstile>s mset ` N"
  by (simp add: true_clss_def)

lemma satisfiable_mset_remdups[simp]:
  "satisfiable ((mset \<circ> remdups) ` N) \<longleftrightarrow> satisfiable (mset ` N)"
unfolding satisfiable_carac[symmetric] by simp

definition find_unit where
"find_unit l = List.find (\<lambda>l. length l = 1) l"

lemma atms_of_multiset[simp]: "atms_of (mset a) = atm_of ` set a"
  by (induct a, auto)


value "backtrack_split [Marked (Pos (Suc 0)) Level]"
value "\<exists>C \<in> set [[Pos (Suc 0), Neg (Suc 0)]]. (\<forall>c \<in> set C. -c \<in> lits_of [Marked (Pos (Suc 0)) Level])"

lemma lits_of_unfold:"(\<forall>c \<in> set C. -c \<in> lits_of Ms) \<longleftrightarrow> Ms \<Turnstile>as CNot (mset C)"
  unfolding true_annots_def Ball_def true_annot_def CNot_def
  using mem_set_multiset_eq by force

definition is_unit_clause :: "'a literal list \<Rightarrow> ('a, 'b, 'c) marked_lit list \<Rightarrow> 'a literal option" where
 "is_unit_clause l M =
   (case List.filter (\<lambda>a. atm_of a \<notin> atm_of ` lits_of M) l of
     a # [] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None
   | _ \<Rightarrow> None)"

definition is_unit_clause_code :: "'a literal list \<Rightarrow> ('a, 'b, 'c) marked_lit list \<Rightarrow> 'a literal option" where
 "is_unit_clause_code l M =
   (case List.filter (\<lambda>a. atm_of a \<notin> atm_of ` lits_of M) l of
     a # [] \<Rightarrow> if (\<forall>c \<in>set (remove1 a l). -c \<in> lits_of M) then Some a else None
   | _ \<Rightarrow> None)"

lemma [code]:
  "is_unit_clause l M = is_unit_clause_code l M"
proof -
  have 1: "\<And>a. (\<forall>c\<in>set (remove1 a l). - c \<in> lits_of M) \<longleftrightarrow> M \<Turnstile>as CNot (mset l - {#a#})" (is "\<And>a. ?P a")
    proof -
      fix a
      show "?P a"
        using lits_of_unfold[of "remove1 a l", of M] by simp
    qed
  thus ?thesis
    unfolding is_unit_clause_code_def is_unit_clause_def 1 by blast
qed

lemma is_unit_clause_some_undef: "is_unit_clause l M = Some a \<Longrightarrow> undefined_lit a M"
  unfolding is_unit_clause_def lits_of_def
proof -
  assume "(case [a\<leftarrow>l . atm_of a \<notin> atm_of ` lit_of ` set M] of [] \<Rightarrow> None | [a] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None | a # ab # xa \<Rightarrow> Map.empty xa) = Some a"
  hence "a \<in> set [a\<leftarrow>l . atm_of a \<notin> atm_of ` lit_of ` set M]"
    apply (case_tac "[a\<leftarrow>l . atm_of a \<notin> atm_of ` lit_of ` set M]", auto)
    apply (case_tac list, auto)
    apply (case_tac "M \<Turnstile>as CNot (mset l - {#aa#})")
    by auto
  hence "atm_of a \<notin> atm_of ` lit_of ` set M" by auto
  thus ?thesis by (simp add: Marked_Propagated_in_iff_in_lits_of atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set lits_of_def)
qed

lemma is_unit_clause_some_CNot: "is_unit_clause l M = Some a \<Longrightarrow> M \<Turnstile>as CNot (mset l - {#a#})"
  unfolding is_unit_clause_def lits_of_def
proof -
  assume "(case [a\<leftarrow>l . atm_of a \<notin> atm_of ` lit_of ` set M] of [] \<Rightarrow> None | [a] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None | a # ab # xa \<Rightarrow> Map.empty xa) = Some a"
  thus ?thesis
    apply (case_tac "[a\<leftarrow>l . atm_of a \<notin> atm_of ` lit_of ` set M]", auto)
    apply (case_tac list, auto)
    apply (case_tac "M \<Turnstile>as CNot (mset l - {#aa#})")
    by auto
qed

lemma is_unit_clause_some_in: "is_unit_clause l M = Some a \<Longrightarrow> a \<in> set l"
  unfolding is_unit_clause_def lits_of_def
proof -
  assume "(case [a\<leftarrow>l . atm_of a \<notin> atm_of ` lit_of ` set M] of [] \<Rightarrow> None | [a] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None | a # ab # xa \<Rightarrow> Map.empty xa) = Some a"
  thus "a \<in> set l"
    apply (case_tac "[a\<leftarrow>l . atm_of a \<notin> atm_of ` lit_of ` set M]", auto)
    apply (case_tac list, auto)
    apply (case_tac "M \<Turnstile>as CNot (mset l - {#aa#})")
    apply auto
    by (metis (no_types, lifting) insertI1 list.simps(15) mem_Collect_eq set_filter)
qed

lemma [simp]: "is_unit_clause [] M = None"
  unfolding is_unit_clause_def by auto

fun find_first_unit_clause :: "'a literal list list \<Rightarrow> ('a, 'b, 'c) marked_lit list \<Rightarrow> ('a literal \<times> 'a literal list) option"  where
"find_first_unit_clause (a # l) M =
  (case is_unit_clause a M of
    None \<Rightarrow> find_first_unit_clause l M
  | Some L \<Rightarrow> Some (L, a))" |
"find_first_unit_clause [] _ = None"

lemma find_first_unit_clause_some: "find_first_unit_clause l M = Some (a, c) \<Longrightarrow> c \<in> set l \<and>  M \<Turnstile>as CNot (mset c - {#a#}) \<and> undefined_lit a M \<and> a \<in> set c"
  apply (induct l, auto)
  apply (case_tac "is_unit_clause aa M", auto split: option.splits)
  using is_unit_clause_some_CNot is_unit_clause_some_undef apply blast
  using is_unit_clause_some_undef apply blast
  using is_unit_clause_some_in by blast

lemma propagate_is_unit_clause_not_None:
  assumes dist: "distinct c" and
  M: "M \<Turnstile>as CNot (mset c - {#a#})" and
  undef: "undefined_lit a M" and
  ac: "a \<in> set c"
  shows "is_unit_clause c M \<noteq> None"
proof -
  have "[a\<leftarrow>c . atm_of a \<notin> atm_of ` lits_of M] = [a]"
    using assms
    proof (induction c)
      case Nil thus ?case by simp
    next
      case (Cons ac c)
      show ?case
        proof (cases "a = ac")
          case True
          thus ?thesis using Cons
            by (auto simp add: lits_of_unfold[symmetric] Marked_Propagated_in_iff_in_lits_of atm_of_eq_atm_of atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
        next
          case False
          hence T: "mset c + {#ac#} - {#a#} = mset c - {#a#} + {#ac#}"
            by (auto simp add: multiset_eq_iff)

          show ?thesis using False Cons
            by (auto simp add: T atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
        qed
    qed
  thus ?thesis
    using M unfolding is_unit_clause_def by auto
qed

lemma find_first_unit_clause_none: "distinct c \<Longrightarrow> c \<in> set l \<Longrightarrow>  M \<Turnstile>as CNot (mset c - {#a#}) \<Longrightarrow> undefined_lit a M \<Longrightarrow> a \<in> set c \<Longrightarrow> find_first_unit_clause l M \<noteq> None"
  by (induction l)
     (auto split: option.split simp add: propagate_is_unit_clause_not_None)


type_synonym cdcl_state_st = "(nat, nat, nat literal list) marked_lit list \<times> nat literal list list \<times> nat literal list list \<times> nat \<times> nat literal list conflicting_clause"

fun convert where
"convert (Propagated L C) = Propagated L (mset C)" |
"convert (Marked K i) = Marked K i"

fun convertC where
"convertC (C_Clause C) = C_Clause (mset C)" |
"convertC C_True = C_True"

lemma convert_CTrue[iff]:
  "convertC e = C_True \<longleftrightarrow> e= C_True"
  by (cases e) auto

lemma convert_Propagated[elim!]:
  "convert z = Propagated L C \<Longrightarrow> (\<exists>C'. z = Propagated L C' \<and> C = mset C')"
  by (cases z) auto


lemma get_rev_level_map_convert:
  "get_rev_level x n (map convert M) = get_rev_level x n M"
  apply (induction M arbitrary: n)
  apply simp
  by (case_tac a) auto

lemma get_level_map_convert[simp]:
  "get_level x (map convert M) = get_level x M"
  using get_rev_level_map_convert[of x 0 "rev M"] by (simp add: rev_map)

lemma get_maximum_level_map_convert[simp]:
  "get_maximum_level D (map convert M) = get_maximum_level D M"
  by (induction D)
     (auto simp add: get_maximum_level_plus)

fun toS :: "cdcl_state_st \<Rightarrow> nat cdcl_state" where
"toS (M, N, U, k, C) = (map convert M, set (map mset N),  set (map mset U), k, convertC C) "
typedef cdcl_state =  "{S::cdcl_state_st. cdcl_all_inv_mes (toS S)}"
  morphisms rough_state_of state_of
proof
    show "([],[], [], 0, C_True) \<in> {S. cdcl_all_inv_mes (toS S)}" by (auto simp add: cdcl_all_inv_mes_def)
qed


instantiation cdcl_state :: equal
begin
definition equal_cdcl_state :: "cdcl_state \<Rightarrow> cdcl_state \<Rightarrow> bool" where
 "equal_cdcl_state S S' = (rough_state_of S = rough_state_of S')"
instance
  by standard (simp add: rough_state_of_inject equal_cdcl_state_def)
end


lemma lits_of_map_convert[simp]: "lits_of (map convert M) = lits_of M"
  apply (induction M)
  apply simp
  by (case_tac a) auto

lemma undefined_lit_map_convert[iff]:
  "undefined_lit L (map convert M) \<longleftrightarrow> undefined_lit L M"
  by (auto simp add: Marked_Propagated_in_iff_in_lits_of)


lemma true_annot_map_convert[simp]: "map convert M \<Turnstile>a N \<longleftrightarrow> M \<Turnstile>a N"
  apply (induction M)
  apply simp
  apply (case_tac a)
  by (simp_all add: true_annot_def)

lemma true_annots_map_convert[simp]: "map convert M \<Turnstile>as N \<longleftrightarrow> M \<Turnstile>as N"
  unfolding true_annots_def by auto

lemma find_first_unit_clause_some_is_propagate:
  assumes H: "find_first_unit_clause (N @ U) M = Some (L, C)"
  shows "propagate (toS (M, N, U, k, C_True)) (toS (Propagated L C # M, N, U, k, C_True))"
  using assms
  apply (auto dest!: find_first_unit_clause_some simp add: propagate.simps)
  by (rule exI[of _ "mset C - {#L#}"], simp)+

definition do_propagate_step where
"do_propagate_step S =
  (case S of
    (M, N, U, k, C_True) \<Rightarrow>
      (case find_first_unit_clause (N @ U) M of
        Some (L, C) \<Rightarrow> (Propagated L C # M, N, U, k, C_True)
      | None \<Rightarrow> (M, N, U, k, C_True))
  | S \<Rightarrow> S)"

lemma do_propgate_step:
  "do_propagate_step S \<noteq> S \<Longrightarrow> propagate (toS S) (toS (do_propagate_step S))"
  apply (cases S, cases "conflicting S")
  using find_first_unit_clause_some_is_propagate[of "clauses S" "learned_clauses S" "trail S" _ _ "backtrack_level S"]
  by (auto simp add: do_propagate_step_def split: option.splits)

lemma do_propagate_step_conflicting_clause[simp]:
  "conflicting S \<noteq> C_True \<Longrightarrow> do_propagate_step S = S"
  unfolding do_propagate_step_def by (cases S, cases "conflicting S") auto

lemma do_propagate_step_no_step:
  assumes dist: "\<forall>c\<in>set (clauses S @ learned_clauses S). distinct c" and
  prop_step: "do_propagate_step S = S"
  shows "no_step propagate (toS S)"
proof (standard, standard)
  fix T
  assume "propagate (toS S) T"
  then obtain M N U k C L where
    toSS: "toS S = (M, N, U, k, C_True)" and
    T: "T = (Propagated L (C + {#L#}) # M, N, U, k, C_True)" and
    MC: "M \<Turnstile>as CNot C" and
    undef: "undefined_lit L M" and
    CL: "C + {#L#} \<in> N \<union> U"
    by (auto simp add: propagate.simps)
  let ?M = "trail S"
  let ?N = "clauses S"
  let ?U = "learned_clauses S"
  let ?k = "backtrack_level S"
  let ?D = "C_True"
  have S: "S = (?M, ?N, ?U, ?k, ?D)"
    using toSS by (cases S, cases "conflicting S") simp_all
  have S: "toS S = toS (?M, ?N, ?U, ?k, ?D)"
    unfolding S[symmetric] by simp

  have M: "M = map convert ?M" and
  N: "N = set (map mset ?N)" and
  U: "U = set (map mset ?U)"
    using toSS[unfolded S] by auto

  obtain D where
  DCL: "mset D = C + {#L#}" and
  D: "D \<in> set (?N @ ?U)"
    using CL unfolding N U by auto
  obtain C' L' where
  setD: "set D = set (L' # C')" and
  C': "mset C' = C" and
  L: "L = L'"
    using DCL by (metis ex_mset mset.simps(2) mset_eq_setD)
  have "find_first_unit_clause (?N @ ?U) ?M \<noteq> None"
    apply (rule dist find_first_unit_clause_none[of D "?N @ ?U" ?M L, OF _ D ])
        using D assms(1) apply auto[1]
        using MC setD DCL M MC unfolding C'[symmetric] apply auto[1]
        using M undef apply auto[1]
        unfolding setD L by auto
  thus False using prop_step S unfolding do_propagate_step_def by (cases S) auto
qed

fun find_conflict where
"find_conflict M [] = None" |
"find_conflict M (N # Ns) = (if (\<forall>c \<in> set N. -c \<in> lits_of M) then Some N else find_conflict M Ns)"

lemma find_conflict_Some:
  "find_conflict M Ns = Some N \<Longrightarrow> N \<in> set Ns \<and> M \<Turnstile>as CNot (mset N)"
  by (induction Ns rule: find_conflict.induct)
     (auto split: split_if_asm simp add: lits_of_unfold)

lemma find_conflict_None:
  "find_conflict M Ns = None \<longleftrightarrow> (\<forall>N \<in> set Ns. \<not>M \<Turnstile>as CNot (mset N))"
  by (induction Ns) (simp_all add: lits_of_unfold)

lemma find_conflict_None_no_confl:
  "find_conflict M (N@U) = None \<longleftrightarrow> no_step conflict (toS (M, N, U, k, C_True))"
 by (auto simp add: find_conflict_None conflict.simps)

definition do_conflict_step where
"do_conflict_step S =
  (case S of
    (M, N, U, k, C_True) \<Rightarrow>
      (case find_conflict M (N @ U) of
        Some a \<Rightarrow> (M, N, U, k, C_Clause a)
      | None \<Rightarrow> (M, N, U, k, C_True))
  | S \<Rightarrow> S)"

lemma do_conflict_step:
  "do_conflict_step S \<noteq> S \<Longrightarrow> conflict (toS S) (toS (do_conflict_step S))"
  apply (cases S, cases "conflicting S")
  unfolding conflict.simps do_conflict_step_def
  by (auto simp add:  dest!:find_conflict_Some  split: option.splits)

lemma do_conflict_step_no_step:
  "do_conflict_step S = S \<Longrightarrow> no_step conflict (toS S)"
  apply (cases S, cases "conflicting S")
  unfolding do_conflict_step_def
  using find_conflict_None_no_confl[of "trail S" "clauses S" "learned_clauses S"
      "backtrack_level S"]
  by (auto split: option.splits)

lemma do_conflict_step_conflicting_clause[simp]:
  "conflicting S \<noteq> C_True \<Longrightarrow> do_conflict_step S = S"
  unfolding do_conflict_step_def by (cases S, cases "conflicting S") auto

lemma do_conflict_step_conflicting[dest]:
  "do_conflict_step S \<noteq> S \<Longrightarrow> conflicting (do_conflict_step S) \<noteq> C_True"
  unfolding do_conflict_step_def by (cases S, cases "conflicting S") (auto split: option.splits)

definition do_cp_step where
"do_cp_step S =
  (do_conflict_step o do_propagate_step o do_conflict_step) S"

lemma cp_step_is_cdcl_cp:
  assumes H: "do_cp_step S \<noteq> S"
  shows "cdcl_cp (toS S) (toS (do_cp_step S))"
proof -
  show ?thesis
  proof (cases "do_conflict_step S \<noteq> S")
    case True
    thus ?thesis
      by (simp add: do_conflict_step do_conflict_step_conflicting do_cp_step_def)
  next
    case False
    hence confl[simp]: "do_conflict_step S = S" by simp
    show ?thesis
      proof (cases "do_propagate_step S = S")
        case True
        thus ?thesis
        using H by (simp add: do_cp_step_def)
      next
        case False
        let ?S = "toS S"
        let ?T = "toS (do_propagate_step S)"
        let ?U = "toS (do_conflict_step (do_propagate_step S))"
        have propa: "propagate (toS S) ?T" using False do_propgate_step by blast
        also have ns: "no_step conflict (toS S)" using confl do_conflict_step_no_step by blast
        ultimately show ?thesis
          using cdcl_cp.intros(2)[of ?S ?T ?U] cdcl_cp.intros(3)[of ?S ?U] unfolding do_cp_step_def
          by (metis comp_apply confl do_conflict_step do_conflict_step_no_step)
      qed
  qed
qed

lemma do_cp_step_eq_no_prop_no_confl:
  "do_cp_step S = S \<Longrightarrow> do_conflict_step S = S \<and> do_propagate_step S = S"
  by (cases S, cases "conflicting S")
     (auto simp add: do_conflict_step_def do_propagate_step_def do_cp_step_def split: option.splits)

lemma no_cdcl_cp_iff_no_propagate_no_conflict:
  "no_step cdcl_cp S \<longleftrightarrow> no_step propagate S \<and> no_step conflict S"
  by (meson cdcl_cp.cases cdcl_cp.conflict' no_step_cdcl_cp_no_conflict_no_propagate(2))

lemma do_cp_step_eq_no_step:
  assumes H: "do_cp_step S = S" and "\<forall>c \<in> set (clauses S @ learned_clauses S). distinct c"
  shows "no_step cdcl_cp (toS S)"
  unfolding no_cdcl_cp_iff_no_propagate_no_conflict
  using assms apply (cases S, cases "conflicting S")
  using do_propagate_step_no_step[of S] by (auto dest!: do_cp_step_eq_no_prop_no_confl[simplified] do_conflict_step_no_step split: option.splits)

lemma cdcl_all_inv_mes_length_trail_le_card_atms_of_clauses:
  assumes inv: "cdcl_all_inv_mes S"
  shows "length (trail S) \<le> card (atms_of_m (clauses S))"
proof -
  have "atm_of ` lits_of (trail S) \<subseteq> atms_of_m (clauses S)" 
    using inv unfolding cdcl_all_inv_mes_def no_strange_atm_def by simp
  also have "no_dup (trail S)" 
    using inv unfolding cdcl_all_inv_mes_def cdcl_M_level_inv_def by auto
    hence "card (atm_of ` (lits_of (trail S))) = length (trail S)"
      by (simp add: distinctlength_eq_card_atm_of_lits_of)
  moreover have "finite (atms_of_m (clauses S))"
    using inv unfolding cdcl_all_inv_mes_def by simp
  ultimately show ?thesis by (metis card_mono)
qed

lemma cdcl_cp_cdcl_st: "cdcl_cp S S' \<Longrightarrow> cdcl\<^sup>*\<^sup>* S S'"
  by (induction rule: cdcl_cp.induct)
   (auto dest!: cdcl.intros)
  
  
lemma cdcl_cp_wf: "wf {(S', S::'v Propo_CDCL.cdcl_state). cdcl_all_inv_mes S \<and> cdcl_cp S S'}" (is "wf ?R")
proof (rule wf_bounded_measure[of _ "\<lambda>S. card (atms_of_m (clauses S))+1" "\<lambda>S. length (trail S) + (if conflicting S = C_True then 0 else 1)"], goal_cases)
  case (1 S S')
  hence "cdcl_all_inv_mes S" and "cdcl_cp S S'" by auto
  also hence "cdcl_all_inv_mes S'" using rtranclp_cdcl_all_inv_mes_inv cdcl_cp_cdcl_st by blast
  ultimately show ?case
    by (auto simp add:cdcl_cp.simps elim!: conflictE propagateE dest: cdcl_all_inv_mes_length_trail_le_card_atms_of_clauses)
qed

lemma cdcl_all_inv_mes_rough_state[simp]: "cdcl_all_inv_mes (toS (rough_state_of S))"
  using rough_state_of by auto

lemma [simp]: "cdcl_all_inv_mes (toS S) \<Longrightarrow> rough_state_of (state_of S) = S"
  by (simp add: state_of_inverse)

lemma rough_state_of_state_of_do_cp_step[simp]:
  "rough_state_of (state_of (do_cp_step (rough_state_of S))) = do_cp_step (rough_state_of S)"
proof -
  have "cdcl_all_inv_mes (toS (do_cp_step (rough_state_of S)))"
    apply (cases "do_cp_step (rough_state_of S) = (rough_state_of S)")
    apply simp
    using cp_step_is_cdcl_cp[of "rough_state_of S"] cdcl_all_inv_mes_rough_state[of S]  by (metis cdcl_all_inv_mes_inv comp_apply conflict do_conflict_step do_cp_step_def do_propgate_step propagate)
  thus ?thesis by auto
qed

fun do_skip_step :: "cdcl_state_st \<Rightarrow> cdcl_state_st" where
"do_skip_step (Propagated L C # Ls,N,U,k, C_Clause D) =
  (if -L \<notin> set D \<and> D \<noteq> [] then (Ls, N, U, k, C_Clause D) else (Propagated L C #Ls, N, U, k, C_Clause D))" |
"do_skip_step S = S"

lemma do_skip_step:
  "do_skip_step S \<noteq> S \<Longrightarrow> skip (toS S) (toS (do_skip_step S))"
  apply (induction S rule: do_skip_step.induct)
  by (auto simp add: other skip skip.intros)

lemma do_skip_step_no:
  "do_skip_step S = S \<Longrightarrow> no_step skip (toS S)"
  by (induction S rule: do_skip_step.induct)
     (auto simp add: other elim: skipE split: split_if_asm)

lemma do_skip_step_trail_is_C_True[iff]:
  "do_skip_step S = (a, b, c, d, C_True) \<longleftrightarrow> S = (a, b, c, d, C_True)"
  by (cases S rule: do_skip_step.cases)
     auto

fun maximum_level_code:: "'a literal list \<Rightarrow> ('a, nat, 'a literal list) marked_lit list \<Rightarrow> nat"  where
"maximum_level_code [] _ = 0" |
"maximum_level_code (L # Ls) M = max (get_level L M) (maximum_level_code Ls M)"

lemma maximum_level_code_eq_get_maximum_level[code, simp]:
  "maximum_level_code D M = get_maximum_level (mset D) M"
  by (induction D)
     (auto simp add: get_maximum_level_plus)


fun do_resolve_step :: "cdcl_state_st \<Rightarrow> cdcl_state_st" where
"do_resolve_step (Propagated L C # Ls, N, U, k, C_Clause D) =
  (if -L \<in> set D \<and> (maximum_level_code (remove1 (-L) D) (Propagated L C # Ls) = k \<or>  k = 0)
  then (Ls, N, U, k, C_Clause (remdups (remove1 L C @ remove1 (-L) D)))
  else (Propagated L C # Ls, N, U, k, C_Clause D))" |
"do_resolve_step S = S"

lemma do_resolve_step:
  "cdcl_all_inv_mes (toS S) \<Longrightarrow> do_resolve_step S \<noteq> S \<Longrightarrow> resolve (toS S) (toS (do_resolve_step S))"
proof (induction S rule: do_resolve_step.induct)
  case (1 L C M N U k D)
  hence
    "- L \<in> set D" and
    M: "maximum_level_code (remove1 (-L) D) (Propagated L C # M) = k \<or> k = 0"
    by (auto split: split_if_asm)
  have "every_mark_is_a_conflict (toS (Propagated L C # M, N, U, k, C_Clause D))"
    using 1(1) unfolding cdcl_all_inv_mes_def by fast
  hence "L \<in> set C" by fastforce
  then obtain C' where C: "mset C = C' + {#L#}"
    by (metis add.commute in_multiset_in_set insert_DiffM)
  obtain D' where D: "mset D = D' + {#-L#}"
    using `- L \<in> set D` by (metis add.commute in_multiset_in_set insert_DiffM)
  have D'L:  "D' + {#- L#} - {#-L#} = D'" by (auto simp add: multiset_eq_iff)

  have CL: "mset C - {#L#} + {#L#} = mset C" using `L \<in> set C` by (auto simp add: multiset_eq_iff)
  have
    "resolve
     (map convert (Propagated L C # M), mset ` set N, mset ` set U, k, C_Clause (mset D))
     (map convert M, mset ` set N, mset ` set U, k,
       C_Clause (remdups_mset (mset D - {#-L#} + (mset C - {#L#}))))"
    apply rule
      apply (simp add: C D)
    using M[simplified] unfolding D'L maximum_level_code_eq_get_maximum_level C[symmetric] CL
    by (metis convert.simps(1) get_maximum_level_map_convert list.simps(9))
  thus ?case
    by (smt "1.prems" add.commute convertC.simps(1) do_resolve_step.simps(1) list.set_map mset_append mset_remdups_remdups_mset mset_remove1 toS.simps)
qed auto


lemma do_resolve_step_no:
  "do_resolve_step S = S \<Longrightarrow> no_step resolve (toS S)"
  apply (auto elim!: resolveE )
    apply (cases S; cases "hd (trail S)"; cases "conflicting S")
        apply (auto split: split_if_asm)
       apply (metis count_mset_0 less_not_refl union_single_eq_member)
      apply (metis convert.simps(1) get_maximum_level_map_convert list.simps(9))
  apply (cases S; cases "hd (trail S)"; cases "conflicting S")
  apply (auto split: split_if_asm)
    apply (metis count_mset_0 less_not_refl union_single_eq_member)
  done

lemma  rough_state_of_state_of_resolve[simp]:
  "cdcl_all_inv_mes (toS S) \<Longrightarrow> rough_state_of (state_of (do_resolve_step S)) = do_resolve_step S"
  apply (rule state_of_inverse)
  by (metis cdcl.simps cdcl_all_inv_mes_inv do_resolve_step resolve mem_Collect_eq)

lemma do_resolve_step_trail_is_C_True[iff]:
  "do_resolve_step S = (a, b, c, d, C_True) \<longleftrightarrow> S = (a, b, c, d, C_True)"
  by (cases S rule: do_resolve_step.cases)
     auto
     
fun find_level_decomp where
"find_level_decomp M [] D k = None" |
"find_level_decomp M (L # Ls) D k =
  (case (get_level L M, maximum_level_code (D @ Ls) M) of
    (i, j) \<Rightarrow> if i = k \<and> j < i then Some (L, j) else find_level_decomp M Ls (L#D) k
    )"

lemma find_level_decomp_some:
  "find_level_decomp M Ls D k = Some (L, j) \<Longrightarrow> L \<in> set Ls \<and> get_maximum_level (mset (remove1 L (Ls @ D))) M = j \<and> get_level L M = k"
  apply (induction Ls arbitrary: D)
  apply simp
  apply (auto split: split_if_asm simp add: add.commute)
  apply (smt ab_semigroup_add_class.add_ac(1) add.commute diff_union_swap mset.simps(2))
  apply (smt add.commute add.left_commute diff_union_cancelL mset.simps(2))
  apply (smt add.commute add.left_commute diff_union_swap mset.simps(2))
  done

lemma find_level_decomp_none:
  "find_level_decomp M Ls E k = None \<Longrightarrow> mset (L#D) = mset (Ls @ E) \<Longrightarrow> \<not>(L \<in> set Ls \<and> get_maximum_level (mset D) M < k \<and> k = get_level L M)"
proof (induction Ls arbitrary: E L D)
  case Nil
  thus ?case by simp
next
  case (Cons L' Ls) note IH = this(1) and find_none = this(2) and LD = this(3)
  show ?case
    using find_none
    using IH[of "L' # E" L D] LD apply (auto simp add: ac_simps split: split_if_asm)
    by (metis add_right_imp_eq union_assoc)
qed

fun bt_cut where
"bt_cut i (Propagated _ _ # Ls) = bt_cut i Ls" |
"bt_cut i (Marked K k # Ls) = (if k = Suc i then Some (Marked K k # Ls) else bt_cut i Ls)" |
"bt_cut i [] = None"

lemma bt_cut_some_decomp:
  "bt_cut i M = Some M' \<Longrightarrow> \<exists>K M2 M1. M = M2 @ M' \<and> M' = Marked K (i+1) # M1"
  by (induction i M rule: bt_cut.induct) (auto split: split_if_asm)

lemma bt_cut_not_none: "M = M2 @ Marked K (Suc i) # M' \<Longrightarrow> bt_cut i M \<noteq> None"
apply (induction M2 arbitrary: M)
apply simp
by (case_tac a) auto

lemma get_all_marked_decomposition_ex:
  "\<exists>N. (Marked K (Suc i) # M', N) \<in> set (get_all_marked_decomposition (M2@Marked K (Suc i) # M'))"
  apply (induction M2)
    apply auto[1]
  apply (case_tac a; case_tac "hd (get_all_marked_decomposition (M2 @ Marked K (Suc i) # M'))")
  apply auto
  by (metis Nil_is_append_conv fst_conv in_set_conv_decomp_first list.collapse set_ConsD)

lemma bt_cut_in_get_all_marked_decomposition:
  "bt_cut i M = Some M' \<Longrightarrow> \<exists>M2. (M', M2) \<in> set (get_all_marked_decomposition M)"
  by (auto dest!: bt_cut_some_decomp simp add: get_all_marked_decomposition_ex)

fun do_backtrack_step where
"do_backtrack_step (M, N, U, k, C_Clause D) =
  (case find_level_decomp M D [] k of
    None \<Rightarrow> (M, N, U, k, C_Clause D)
  | Some (L, j) \<Rightarrow>
    (case bt_cut j M of
      Some (Marked _ _ # Ls) \<Rightarrow> (Propagated L D # Ls, N, D # U, j, C_True)
    | _ \<Rightarrow> (M, N, U, k, C_Clause D))
  )" |
"do_backtrack_step S = S"

lemma get_all_marked_decomposition_map_convert:
  "(get_all_marked_decomposition (map convert M)) = map (\<lambda>(a, b). (map convert a, map convert b)) (get_all_marked_decomposition M)"
  apply (induction M)
  apply simp
  apply (case_tac a; case_tac "hd (get_all_marked_decomposition M)"; case_tac "hd (get_all_marked_decomposition (map convert M))")
  by (auto simp add: list.map_sel(1) list.map_sel(2))

lemma do_backtrack_step:
  assumes db: "do_backtrack_step S \<noteq> S"
  and inv: "cdcl_all_inv_mes (toS S)"
  shows "backtrack (toS S) (toS (do_backtrack_step S))"
  proof (cases S, cases "conflicting S", goal_cases)
    case (1 M N U k E)
    thus ?case using db by auto
  next
    case (2 M N U k E C) note S =this(1) and confl = this(2)
    have E: "E = C_Clause C" using S confl by auto

    obtain L j where fd: "find_level_decomp M C [] k = Some (L, j)"
      using db unfolding S E  by (cases C) (auto split: split_if_asm option.splits)
    have "L \<in> set C" and "get_maximum_level (mset (remove1 L C)) M = j"
      using find_level_decomp_some[OF fd] by auto
    obtain C' where C: "mset C = mset C' + {#L#}"
      using `L \<in> set C` by (metis add.commute ex_mset in_multiset_in_set insert_DiffM)
    obtain M\<^sub>2 where M\<^sub>2: "bt_cut j M = Some M\<^sub>2"
      using db fd unfolding S E by (auto split: option.splits)
    obtain M1 K where M1: "M\<^sub>2 = Marked K (Suc j) # M1"
      using bt_cut_some_decomp[OF M\<^sub>2] by (cases M\<^sub>2) auto
    obtain c where c: "M = c @ Marked K (Suc j) # M1"
       using bt_cut_in_get_all_marked_decomposition[OF M\<^sub>2] get_all_marked_decomposition_exists_prepend unfolding M1 by fastforce
    have "get_all_levels_of_marked (map convert M) = rev [1..<Suc k]"
      using inv unfolding cdcl_all_inv_mes_def cdcl_M_level_inv_def S by auto
    from arg_cong[OF this, of "\<lambda>a. Suc j \<in> set a"] have "j \<le> k" unfolding c by auto
    have levL: "get_level L (map convert M) = k"
      using db fd M\<^sub>2 unfolding S E by (auto
          split: option.splits list.splits marked_lit.splits
          dest!: find_level_decomp_some)[1]
    have max_l_j: "maximum_level_code C' M = j"
      using db fd M\<^sub>2 C unfolding S E by (auto
          split: option.splits list.splits marked_lit.splits
          dest!: find_level_decomp_some)[1]
    obtain M2 where M2: "(M\<^sub>2, M2) \<in> set (get_all_marked_decomposition M)"
      using bt_cut_in_get_all_marked_decomposition[OF M\<^sub>2] by metis
    have "backtrack
           (map convert M, mset ` set N, mset ` set U, k, C_Clause (mset C))
           (Propagated L (mset C) # map convert M1, mset ` set N, mset ` set U \<union> {mset C}, j, C_True)"
      unfolding C M1 List.list.map set_append
      apply rule
           apply auto[1]
          using bt_cut_in_get_all_marked_decomposition[OF M\<^sub>2] unfolding M1 defer
        using levL apply simp
      using max_l_j levL `j \<le> k` apply (simp add: get_maximum_level_plus)
      using max_l_j apply simp
      using Set.imageI[of "(M\<^sub>2, M2)" "set (get_all_marked_decomposition M)" "(\<lambda>(a, b). (map convert a, map convert b))", OF M2]
      unfolding M1 by (auto simp add: get_all_marked_decomposition_map_convert)
    thus ?case
      using M\<^sub>2 fd unfolding S E M1 by auto
    obtain M2 where "(M\<^sub>2, M2) \<in> set (get_all_marked_decomposition M)"
      using bt_cut_in_get_all_marked_decomposition[OF M\<^sub>2] by metis
qed


lemma do_backtrack_step_no:
  assumes db: "do_backtrack_step S = S"
  and inv: "cdcl_all_inv_mes (toS S)"
  shows "no_step backtrack (toS S)"
proof (rule ccontr, cases S, cases "conflicting S", goal_cases)
  case 1
  thus ?case using db by (auto split: option.splits elim!: btE)
next
  case (2 M N U k E C) note bt = this(1) and S = this(2) and confl = this(3)
  obtain D L K b z M1 j where
    levL: "get_level L M = get_maximum_level (D + {#L#}) M" and
    k: "k = get_maximum_level (D + {#L#}) M" and
    j: "j = get_maximum_level D M" and
    CE: "convertC E = C_Clause (D + {#L#})" and
    decomp: "(z # M1, b) \<in> set (get_all_marked_decomposition M)" and
    z: "Marked K (Suc j) = convert z" using bt unfolding S
      by (auto split: option.splits elim!: btE simp add: get_all_marked_decomposition_map_convert)
  have z: "z = Marked K (Suc j)" using z by (cases z) auto
  obtain c where c: "M = c @ b @ Marked K (Suc j) # M1"
    using get_all_marked_decomposition_exists_prepend[OF decomp] unfolding z by blast
  have "get_all_levels_of_marked (map convert M) = rev [1..<Suc k]"
    using inv unfolding cdcl_all_inv_mes_def cdcl_M_level_inv_def S by auto
  from arg_cong[OF this, of "\<lambda>a. Suc j \<in> set a"] have "k > j" unfolding c by auto
  obtain C D' where
    E: "E = C_Clause C" and
    C: "mset C = mset (L # D')"
    using CE apply (cases E)
      apply simp
    by (metis conflicting_clause.inject convertC.simps(1) ex_mset mset.simps(2))
  have D'D: "mset D' = D"
    using C CE E by auto
  have "find_level_decomp M C [] k \<noteq> None"
    apply rule
    apply (drule find_level_decomp_none[of _ _ _ _ L D'])
      using C apply simp
    using C `k > j` mset_eq_setD unfolding k[symmetric] D'D j[symmetric] levL by fastforce
  then obtain L' j' where fd_some: "find_level_decomp M C [] k = Some (L', j')"
    by (cases "find_level_decomp M C [] k") auto
  have L': "L' = L"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "L' \<in># D"
        by (metis C D'D fd_some find_level_decomp_some in_multiset_in_set insert_iff list.simps(15))
      hence "get_level L' M \<le> get_maximum_level D M"
        using get_maximum_level_ge_get_level by blast
      thus False using `k > j` j find_level_decomp_some[OF fd_some] by auto
    qed
  hence j': "j' = j"  using find_level_decomp_some[OF fd_some] j C D'D by auto

  have btc_none: "bt_cut j M \<noteq> None"
   apply (rule bt_cut_not_none[of M "_ @ _"])
    using c by simp
  show ?case using db unfolding S  E
    by (auto split: option.splits list.splits marked_lit.splits
      simp add: fd_some  L' j' btc_none
      dest: bt_cut_some_decomp)
qed

lemma  rough_state_of_state_of_backtrack[simp]:
  "cdcl_all_inv_mes (toS S) \<Longrightarrow> rough_state_of (state_of (do_backtrack_step S)) = do_backtrack_step S"
  apply (rule state_of_inverse)
  by (metis cdcl.simps cdcl_all_inv_mes_inv do_backtrack_step backtrack mem_Collect_eq)

fun find_first_unused_var :: "'a literal list list \<Rightarrow> 'a literal set \<Rightarrow> 'a literal option"  where
"find_first_unused_var (a # l) M =
  (case List.find (\<lambda>lit. lit \<notin> M \<and> -lit \<notin> M) a of
    None \<Rightarrow> find_first_unused_var l M
  | Some a \<Rightarrow> Some a)" |
"find_first_unused_var [] _ = None"

lemma find_none[iff]: "List.find (\<lambda>lit. lit \<notin> M \<and> -lit \<notin> M) a = None \<longleftrightarrow>  atm_of ` set a \<subseteq> atm_of `  M"
   apply (induct a, auto)
   using atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set by (fastforce simp add:  atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)+

lemma find_some: "List.find (\<lambda>lit. lit \<notin> M \<and> -lit \<notin> M) a = Some b \<Longrightarrow> b \<in> set a \<and> b \<notin> M \<and> -b \<notin> M"  by (metis find_Some_iff nth_mem)

lemma find_first_unused_var_None:
  "find_first_unused_var l M = None \<longleftrightarrow> (\<forall>a \<in> set l. atm_of ` set a \<subseteq> atm_of `  M)"
  apply(induct l, auto split: option.split)
  using find_some[of M] by (smt atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set image_subset_iff)+

lemma find_first_unused_var_Some:
  "find_first_unused_var l M = Some a \<Longrightarrow> (\<exists>m \<in> set l. a \<in> set m \<and> a \<notin> M \<and> -a \<notin> M)"
  apply(induct l, auto split: option.split)
  using find_some[of M] by (metis (lifting) option.case_eq_if option.collapse)+

lemma find_first_unused_var_undefined:
  "find_first_unused_var l (lits_of Ms) = Some a \<Longrightarrow> undefined_lit a Ms"
  using find_first_unused_var_Some[of l "lits_of Ms" a] Marked_Propagated_in_iff_in_lits_of by blast

fun do_decide_step where
"do_decide_step (M, N, U, k, C_True) =
  (case find_first_unused_var N (lits_of M) of
    None \<Rightarrow> (M, N, U, k, C_True)
  | Some L \<Rightarrow> (Marked L (Suc k) # M, N, U, k+1, C_True))" |
"do_decide_step S = S"

lemma do_decide_step:
  "do_decide_step S \<noteq> S \<Longrightarrow> decided (toS S) (toS (do_decide_step S))"
  apply (cases S, cases "conflicting S")
  apply (auto split: option.splits simp add: decided.simps dest: find_first_unused_var_undefined)
  by (metis atms_of_atms_of_m_mono atms_of_multiset contra_subsetD find_first_unused_var_Some image_eqI)
lemma atms_of_m_mset_unfold:
  "atms_of_m (mset ` b) =  (\<Union>x\<in>b. atm_of ` set x)"
  unfolding atms_of_m_def by simp

lemma do_decide_step_no:
  "do_decide_step S = S \<Longrightarrow> no_step decided (toS S)"
  by (cases S, cases "conflicting S")
    (fastforce
      simp add: atms_of_def find_first_unused_var_None atms_of_m_mset_unfold atm_of_eq_atm_of
        Marked_Propagated_in_iff_in_lits_of atms_of_m_def atm_of_in_atm_of_set_in_uminus
        image_subset_iff
      split: option.splits
      elim!: decidedE )+

lemma rough_state_of_state_of_do_decide_step[simp]:
  "cdcl_all_inv_mes (toS S) \<Longrightarrow> rough_state_of (state_of (do_decide_step S)) = do_decide_step S"
  apply (subst state_of_inverse)
    apply (metis cdcl_all_inv_mes_inv decided do_decide_step mem_Collect_eq other)
  apply simp
  done

lemma rough_state_of_state_of_do_skip_step[simp]:
  "cdcl_all_inv_mes (toS S) \<Longrightarrow> rough_state_of (state_of (do_skip_step S)) = do_skip_step S"
  apply (subst state_of_inverse)
    apply (metis cdcl_all_inv_mes_inv skip do_skip_step mem_Collect_eq other)
  apply simp
  done
  
subsection \<open>Code generation\<close>

thm rough_state_of_inverse[simp add]
definition Con  where
  "Con xs = state_of (if cdcl_all_inv_mes (toS (fst xs, snd xs)) then xs else ([], [], [], 0, C_True))"

lemma [code abstype]:
 "Con (rough_state_of S) = S"
  using rough_state_of[of S] unfolding Con_def by (simp add: rough_state_of_inverse)

definition do_cp_step' where
"do_cp_step' S = state_of (do_cp_step (rough_state_of S))"

function do_full_cp_step :: "cdcl_state \<Rightarrow> cdcl_state" where
"do_full_cp_step S =
  (let S' = do_cp_step' S in
   if S = S' then S else do_full_cp_step S')"
by auto
termination
proof (relation "{(T', T). (rough_state_of T', rough_state_of T) \<in> {(S', S). (toS S', toS S) \<in> {(S', S). cdcl_all_inv_mes S \<and> cdcl_cp S S'}}}", goal_cases)
  case 1
  show ?case
    using wf_if_measure_f[OF wf_if_measure_f[OF cdcl_cp_wf, of "toS"], of rough_state_of] .
next
  case 2
  thus ?case apply auto
    using rough_state_of do_cp_step'_def apply auto[1]
    by (metis cp_step_is_cdcl_cp rough_state_of_inverse)
qed


lemma do_full_cp_step_fix_point_of_do_full_cp_step:
  "do_cp_step(rough_state_of (do_full_cp_step S)) = (rough_state_of (do_full_cp_step S))"
 apply (rule do_full_cp_step.induct[of "\<lambda>S. do_cp_step(rough_state_of (do_full_cp_step S)) = (rough_state_of (do_full_cp_step S))"])
by (metis (full_types) do_full_cp_step.elims rough_state_of_state_of_do_cp_step do_cp_step'_def)

lemma in_clauses_rough_state_of_is_distinct:
  "c\<in>set (clauses (rough_state_of S) @ learned_clauses (rough_state_of S)) \<Longrightarrow> distinct c"
apply (cases "rough_state_of S")
using rough_state_of[of S] by (auto simp add: distinct_mset_set_distinct cdcl_all_inv_mes_def distinct_cdcl_state_def)


lemma do_full_cp_step_full0:
  "full0 cdcl_cp (toS (rough_state_of S))
    (toS (rough_state_of (do_full_cp_step S)))"
unfolding full0_def apply standard
apply (induction "S" rule: do_full_cp_step.induct)
 apply (smt cp_step_is_cdcl_cp do_cp_step'_def do_full_cp_step.simps rough_state_of_state_of_do_cp_step rtranclp.rtrancl_refl rtranclp_into_tranclp2 tranclp_into_rtranclp)

 apply (rule do_cp_step_eq_no_step[OF do_full_cp_step_fix_point_of_do_full_cp_step[of S]])
 using in_clauses_rough_state_of_is_distinct unfolding do_cp_step'_def by blast


lemma [code abstract]:
 "rough_state_of (do_cp_step' S) = do_cp_step (rough_state_of S)"
 unfolding do_cp_step'_def by auto

fun do_other_step where
"do_other_step S =
   (let T = do_skip_step S in
     if T \<noteq> S
     then T
     else
       (let U = do_resolve_step T in
       if U \<noteq> T
       then U else
       (let V = do_backtrack_step U in
       if V \<noteq> U then V else do_decide_step V)))"

lemma do_other_step:
  assumes inv: "cdcl_all_inv_mes (toS S)" and
  st: "do_other_step S \<noteq> S"
  shows "cdcl_o (toS S) (toS (do_other_step S))"
  using st inv by (auto split: split_if_asm
    simp add: Let_def
    intro: do_skip_step do_resolve_step do_backtrack_step do_decide_step)

lemma do_other_step_no:
  assumes inv: "cdcl_all_inv_mes (toS S)" and
  st: "do_other_step S = S"
  shows "no_step cdcl_o (toS S)"
  using st inv by (auto split: split_if_asm
    simp add: Let_def elim!: cdcl_o.cases
    dest!: do_skip_step_no do_resolve_step_no do_backtrack_step_no do_decide_step_no)

lemma rough_state_of_state_of_do_other_step[simp]:
  "rough_state_of (state_of (do_other_step (rough_state_of S))) = do_other_step (rough_state_of S)"
  apply (cases "do_other_step (rough_state_of S) = rough_state_of S")
   apply simp
  using rough_state_of[of S] do_other_step[of "rough_state_of S"]  by (metis CollectI
    cdcl_all_inv_mes_inv cdcl_all_inv_mes_rough_state other state_of_inverse)

definition do_other_step' where
"do_other_step' S =
  state_of (do_other_step (rough_state_of S))"

lemma rough_state_of_do_other_step'[code abstract]:
 "rough_state_of (do_other_step' S) = do_other_step (rough_state_of S)"
 apply (cases "do_other_step (rough_state_of S) = rough_state_of S")
   unfolding do_other_step'_def apply simp
 using do_other_step[of "rough_state_of S"] by (metis cdcl_all_inv_mes_inv cdcl_all_inv_mes_rough_state mem_Collect_eq other state_of_inverse)

definition do_cdcl_s_step where
"do_cdcl_s_step S =
   (let T = do_full_cp_step S in
     if T \<noteq> S
     then T
     else
       (let U = (do_other_step' T) in
        (do_full_cp_step U))) "

typedef cdcl_state_I =  "{S::cdcl_state_st. cdcl_all_inv_mes (toS S) \<and> 
  cdcl_s\<^sup>*\<^sup>* (S0_cdcl (clauses (toS S))) (toS S)}"
  morphisms rough_state_of_I state_of_I
proof
    show "([],[], [], 0, C_True) \<in> {S. cdcl_all_inv_mes (toS S) \<and> cdcl_s\<^sup>*\<^sup>* (S0_cdcl (clauses (toS S))) (toS S)}" by (auto simp add: cdcl_all_inv_mes_def)
qed

instantiation cdcl_state_I :: equal
begin
definition equal_cdcl_state_I :: "cdcl_state_I \<Rightarrow> cdcl_state_I \<Rightarrow> bool" where
 "equal_cdcl_state_I S S' = (rough_state_of_I S = rough_state_of_I S')"
instance
  by standard (simp add: rough_state_of_I_inject equal_cdcl_state_I_def)
end

definition ConI  where
  "ConI S = state_of_I (if cdcl_all_inv_mes (toS (fst S, snd S)) \<and> cdcl_s\<^sup>*\<^sup>* (S0_cdcl (clauses (toS S))) (toS S) then S else ([], [], [], 0, C_True))"

lemma [code abstype]:
 "ConI (rough_state_of_I S) = S"
  using rough_state_of_I[of S] unfolding ConI_def by (simp add: rough_state_of_I_inverse)


definition id_of_I_to:: "cdcl_state_I \<Rightarrow> cdcl_state" where
"id_of_I_to S = state_of (rough_state_of_I S)"

lemma [code abstract]:
  "rough_state_of (id_of_I_to S) = rough_state_of_I S"
  unfolding id_of_I_to_def using rough_state_of_I by auto
  
definition do_cdcl_s_step' where
"do_cdcl_s_step' S = state_of_I (rough_state_of (do_cdcl_s_step (id_of_I_to S)))"


  
lemma full0_unfold:
  "full0 r a b \<longleftrightarrow> (a = b \<and> no_step r a) \<or> full r a b"
  unfolding full_def full0_def rtranclp_unfold by blast

lemma toS_do_full_cp_step_not_eq: "do_full_cp_step S \<noteq> S \<Longrightarrow>
    toS (rough_state_of S) \<noteq> toS (rough_state_of (do_full_cp_step S))"
by (metis (mono_tags, lifting) cp_step_is_cdcl_cp do_cp_step'_def do_full_cp_step.simps do_full_cp_step_full0 full0_def rough_state_of_inverse)

text \<open>@{term do_full_cp_step} should not be unfolded anymore:\<close>
declare do_full_cp_step.simps[simp del]

lemma do_cdcl_s_step:
  assumes "do_cdcl_s_step S \<noteq> S"
  shows "cdcl_s (toS (rough_state_of S)) (toS (rough_state_of (do_cdcl_s_step S)))"
proof (cases "do_full_cp_step S = S")
  case False
  thus ?thesis  
    using assms do_full_cp_step_full0[of S] unfolding full0_unfold do_cdcl_s_step_def 
    by (auto intro!: cdcl_s.intros dest: toS_do_full_cp_step_not_eq)
next
  case True
  have "cdcl_o (toS (rough_state_of S)) (toS (rough_state_of (do_other_step' S)))"
    by (metis (mono_tags, hide_lams) True assms cdcl_all_inv_mes_rough_state do_cdcl_s_step_def do_other_step do_other_step'_def rough_state_of_inverse rough_state_of_state_of_do_other_step)
  also have
    np: "no_step propagate (toS (rough_state_of S))" and
    nc: "no_step conflict (toS (rough_state_of S))"
    by (metis True do_cp_step_eq_no_step do_full_cp_step_fix_point_of_do_full_cp_step
       in_clauses_rough_state_of_is_distinct no_cdcl_cp_iff_no_propagate_no_conflict)+
  moreover have "cdcl_cp\<^sup>\<down> (toS (rough_state_of (do_other_step' S))) (toS (rough_state_of (do_full_cp_step (do_other_step' S))))"
    using do_full_cp_step_full0 by auto
  ultimately show ?thesis
    using assms True unfolding do_cdcl_s_step_def
    by (auto intro!: cdcl_s.other' dest: toS_do_full_cp_step_not_eq)
qed
lemma length_trail_toS:
  "length (trail (toS S)) = length (trail S)"
  by (cases S) auto

lemma conflicting_noTrue_iff_toS:
  "conflicting (toS S) \<noteq> C_True \<longleftrightarrow> conflicting S \<noteq> C_True"
  by (cases S) auto  
lemma trail_toS_neq_imp_trail_neq: 
  "trail (toS S) \<noteq> trail (toS S') \<Longrightarrow> trail S \<noteq> trail S'"
by (cases S, cases S') auto

lemma do_skip_step_trail_changed_or_conflict:
  assumes d: "do_other_step S \<noteq> S"
  and inv: "cdcl_all_inv_mes (toS S)"
  shows "trail S \<noteq> trail (do_other_step S)"
proof -
  have M: "\<And>M K M1 c. M = c @ K # M1 \<Longrightarrow> Suc (length M1) \<le> length M"
    by auto
  have "cdcl_o (toS S) (toS (do_other_step S))" using do_other_step[OF inv d] .
  thus ?thesis
    apply (induction "toS S" "toS (do_other_step S)" rule: cdcl_o.induct)
    apply (auto simp del: do_other_step.simps 
        elim!: skipE resolveE decidedE backtrackE
        dest!: get_all_marked_decomposition_exists_prepend
        simp add: length_trail_toS[symmetric] conflicting_noTrue_iff_toS[symmetric] 
          trail_toS_neq_imp_trail_neq)
    by (smt append_Cons append_Nil2 append_assoc list.inject marked_lit.distinct(1) rev_append rev_eq_Cons_iff same_append_eq trail_conv trail_toS_neq_imp_trail_neq)  
qed     

lemma do_full_cp_step_induct: 
  "(\<And>S. (S \<noteq>  do_cp_step' S \<Longrightarrow> P (do_cp_step' S)) \<Longrightarrow> P S) \<Longrightarrow> P a0"
  using do_full_cp_step.induct by metis
  
lemma do_cp_step_neq_trail_increase:
  "\<exists>c. trail (do_cp_step S) = c @ trail  S \<and>(\<forall>m \<in> set c. \<not> is_marked m)"
  by (cases S, cases "conflicting S")
     (auto simp add: do_cp_step_def do_conflict_step_def do_propagate_step_def split: option.splits)

lemma do_full_cp_step_neq_trail_increase:
  "\<exists>c. trail (rough_state_of (do_full_cp_step S)) = c @ trail (rough_state_of S) \<and> (\<forall>m \<in> set c. \<not> is_marked m)"
apply (induction rule: do_full_cp_step_induct)
apply (case_tac "do_cp_step' S = S")
  apply (simp add: do_full_cp_step.simps)
(* TODO Jasmin )sledgehammer[z3, debug, max_facts=100] (do_cp_step_neq_trail_increase do_full_cp_step.simps do_cp_step'_def rough_state_of_state_of_do_cp_step append_assoc             Un_iff  set_append            )*)
by (smt Un_iff append_assoc do_cp_step'_def do_cp_step_neq_trail_increase do_full_cp_step.simps rough_state_of_state_of_do_cp_step set_append)

thm state_of_inverse
lemma do_cp_step_conflicting:
  "conflicting (rough_state_of S) \<noteq> C_True \<Longrightarrow> do_cp_step' S = S"
  unfolding do_cp_step'_def do_cp_step_def by (simp add: rough_state_of_inverse)

lemma do_full_cp_step_conflicting:
  "conflicting (rough_state_of S) \<noteq> C_True \<Longrightarrow> do_full_cp_step S = S"
  unfolding do_cp_step'_def do_cp_step_def 
  apply (induction rule: do_full_cp_step_induct)
  by (case_tac "S \<noteq> do_cp_step' S")
     (auto simp add: rough_state_of_inverse do_full_cp_step.simps dest: do_cp_step_conflicting)

(*TODO Move*)

lemma do_decide_step_not_conflicting_one_more_decide:
  "conflicting S = C_True \<Longrightarrow> do_decide_step S \<noteq> S \<Longrightarrow> 1 + length (filter is_marked (trail S)) = length (filter is_marked (trail (do_decide_step S)))"
  unfolding do_other_step'_def by (cases S,auto simp add: rough_state_of_inverse Let_def split: split_if_asm option.splits)

lemma do_decide_step_not_conflicting_one_more_decide_bt:
  "conflicting S \<noteq> C_True \<Longrightarrow> do_decide_step S \<noteq> S \<Longrightarrow> length (filter is_marked (trail S)) < length (filter is_marked (trail (do_decide_step S)))"
  unfolding do_other_step'_def by (cases S, cases "conflicting S", auto simp add: rough_state_of_inverse Let_def split: split_if_asm option.splits)
  
lemma do_other_step_not_conflicting_one_more_decide_bt:
  assumes "conflicting (rough_state_of S) \<noteq> C_True" and
  "conflicting (rough_state_of (do_other_step' S)) = C_True" and
  "do_other_step' S \<noteq> S"
  shows "length (filter is_marked (trail (rough_state_of S))) > length (filter is_marked (trail (rough_state_of (do_other_step' S))))"
proof (cases S, goal_cases)
  case (1 y) note S = this(1) and inv = this(2)
  obtain M N U k E where y: "y = (M, N, U, k, C_Clause E)" 
    using assms(1) S inv by (cases y, cases "conflicting y") auto
  have M: "rough_state_of (state_of (M, N, U, k,  C_Clause E)) = (M, N, U, k,  C_Clause E)"
    using inv y by (auto simp add: state_of_inverse)
  have bt: "do_other_step' S = state_of (do_backtrack_step (rough_state_of S))"
    using assms(1,2) apply (cases "rough_state_of (do_other_step' S)", auto simp add: Let_def do_other_step'_def)
    apply (cases "rough_state_of S" rule: do_decide_step.cases)
    apply auto
    done
  show ?case
    using assms(2) S unfolding bt y inv apply simp
    by (fastforce simp add: rough_state_of_inverse M Let_def bt  split: split_if_asm option.splits list.splits marked_lit.splits simp del: do_decide_step.simps  dest!: bt_cut_some_decomp dest: arg_cong[of _ _ "\<lambda>u. length (filter is_marked u)"])
qed
    
  
lemma do_other_step_not_conflicting_one_more_decide:
  assumes "conflicting (rough_state_of S) = C_True" and
  "do_other_step' S \<noteq> S"
  shows "1 + length (filter is_marked (trail (rough_state_of S))) = length (filter is_marked (trail (rough_state_of (do_other_step' S))))"
proof (cases S, goal_cases)
  case (1 y) note S = this(1) and inv = this(2)
  obtain M N U k where y: "y = (M, N, U, k, C_True)" using assms(1) S inv by (cases y) auto
  have M: "rough_state_of (state_of (M, N, U, k, C_True)) = (M, N, U, k, C_True)"
    using inv y by (auto simp add: state_of_inverse)
  show ?case
    using assms(2) S unfolding do_other_step'_def y inv
    apply (auto simp add: rough_state_of_inverse M Let_def  split: split_if_asm option.splits simp del: do_decide_step.simps)
  using do_decide_step_not_conflicting_one_more_decide by (metis M Suc_eq_plus1_left assms(1) cdcl_all_inv_mes_rough_state rough_state_of_state_of_do_decide_step trail_conv)
qed

lemma [simp]:
  "rough_state_of (state_of (do_skip_step (rough_state_of S))) = do_skip_step (rough_state_of S)"
  by (smt do_other_step.simps rough_state_of_inverse rough_state_of_state_of_do_other_step)

  
  
lemma conflicting_do_resolve_step_iff[iff]:
  "conflicting (do_resolve_step S) = C_True \<longleftrightarrow> conflicting S = C_True"
  by (cases S rule: do_resolve_step.cases)
   (auto simp add: Let_def split: option.splits)

lemma conflicting_do_skip_step_iff[iff]:
  "conflicting (do_skip_step S) = C_True \<longleftrightarrow> conflicting S = C_True"
  by (cases S rule: do_skip_step.cases)
   (auto simp add: Let_def split: option.splits)

lemma conflicting_do_decide_step_iff[iff]:
  "conflicting (do_decide_step S) = C_True \<longleftrightarrow> conflicting S = C_True"
  by (cases S rule: do_decide_step.cases)
   (auto simp add: Let_def split: option.splits)
   
lemma conflicting_do_backtrack_step_imp[simp]:
  "do_backtrack_step S \<noteq> S \<Longrightarrow> conflicting (do_backtrack_step S) = C_True"
  by (cases S rule: do_backtrack_step.cases)
   (auto simp add: Let_def split: list.splits option.splits marked_lit.splits)   
 
   (*TODO swap direction?*)
lemma do_skip_step_eq_iff_trail_eq:
  "do_skip_step S = S \<longleftrightarrow> trail (do_skip_step S) = trail S"    
  by (cases S rule: do_skip_step.cases) auto

lemma do_decide_step_eq_iff_trail_eq:
  "do_decide_step S = S \<longleftrightarrow> trail (do_decide_step S) = trail S"    
  by (cases S rule: do_decide_step.cases) (auto split: option.split)

lemma do_backtrack_step_eq_iff_trail_eq:
  "do_backtrack_step S = S \<longleftrightarrow> trail (do_backtrack_step S) = trail S"    
  by (cases S rule: do_backtrack_step.cases) 
    (auto split: option.split list.splits marked_lit.splits dest!: bt_cut_in_get_all_marked_decomposition get_all_marked_decomposition_exists_prepend)

lemma do_resolve_step_eq_iff_trail_eq:
  "do_resolve_step S = S \<longleftrightarrow> trail (do_resolve_step S) = trail S"    
  by (cases S rule: do_resolve_step.cases) auto
  
lemma do_other_step_eq_iff_trail_eq:
  "trail (do_other_step S) = trail S \<longleftrightarrow> do_other_step S = S"    
  by (auto simp add: Let_def do_skip_step_eq_iff_trail_eq[symmetric] do_decide_step_eq_iff_trail_eq[symmetric] do_backtrack_step_eq_iff_trail_eq[symmetric] do_resolve_step_eq_iff_trail_eq[symmetric])
  

lemma [dest!]:
  assumes H: "do_full_cp_step (do_other_step' S) = S"
  shows "do_other_step' S = S \<and> do_full_cp_step S = S"
proof -
  let ?T = "do_other_step' S"
  { assume confl: "conflicting (rough_state_of ?T) \<noteq> C_True" 
    hence tr: "trail (rough_state_of (do_full_cp_step ?T)) = trail (rough_state_of ?T)"
      using do_full_cp_step_conflicting by auto
    have "trail (rough_state_of (do_full_cp_step (do_other_step' S))) = trail (rough_state_of S)"   
      using arg_cong[OF H, of "\<lambda>S. trail (rough_state_of S)"] . 
    hence "trail (rough_state_of (do_other_step' S)) = trail (rough_state_of S)"
       by (auto simp add: do_full_cp_step_conflicting confl)
    hence "do_other_step' S = S"
      by (simp add: do_other_step_eq_iff_trail_eq do_other_step'_def rough_state_of_inverse del: do_other_step.simps)
  }
  also {
    assume eq[simp]: "do_other_step' S = S" 
    obtain c where c: "trail (rough_state_of (do_full_cp_step S)) = c @ trail (rough_state_of S)"
      using do_full_cp_step_neq_trail_increase by auto
      
    also have "trail (rough_state_of (do_full_cp_step S)) = trail (rough_state_of S)"   
      using arg_cong[OF H, of "\<lambda>S. trail (rough_state_of S)"] by simp
    finally have "c = []" by blast
    hence "do_full_cp_step S = S" using assms by auto
    }
  moreover {
    assume confl: "conflicting (rough_state_of ?T) = C_True" and neq: "do_other_step' S \<noteq> S" 
    obtain c where 
      c: "trail (rough_state_of (do_full_cp_step ?T)) = c @ trail (rough_state_of ?T)" and
      nm: "\<forall>m\<in>set c. \<not> is_marked m"
      using do_full_cp_step_neq_trail_increase by auto
    have "length (filter is_marked (trail (rough_state_of (do_full_cp_step ?T)))) = length (filter is_marked (trail (rough_state_of ?T)))" using nm unfolding c by force
    also have "length (filter is_marked (trail (rough_state_of S))) \<noteq> length (filter is_marked  (trail (rough_state_of ?T)))"
      using do_other_step_not_conflicting_one_more_decide[OF _ neq]  do_other_step_not_conflicting_one_more_decide_bt[of S, OF _ confl neq]
      by linarith
    finally have False unfolding H by blast 
  }
  ultimately show ?thesis by blast
qed
  
lemma do_cdcl_s_step_no:
  assumes S: "do_cdcl_s_step S = S"
  shows "no_step cdcl_s (toS (rough_state_of S))"
  apply (auto simp add: cdcl_s.simps)
    using do_full_cp_step_full0[of S] unfolding full0_def S full_def rtranclp_unfold apply (metis (mono_tags, lifting) assms do_cdcl_s_step_def tranclpD)
  
  using assms unfolding do_cdcl_s_step_def apply (auto simp add: Let_def rough_state_of_do_other_step' split:split_if_asm)[1]
    apply (metis cdcl_all_inv_mes_rough_state do_other_step_no rough_state_of_do_other_step')
  by (metis cdcl_all_inv_mes_rough_state do_other_step_no rough_state_of_do_other_step')
  
lemma toS_rough_state_of_state_of_rough_state_of_I[simp]:
  "toS (rough_state_of (state_of (rough_state_of_I S))) = toS (rough_state_of_I S)"
  using rough_state_of_I[of S] by (auto simp add: state_of_inverse)

lemma clauses_toS_rough_state_of_do_cdcl_s_step[simp]:
  "clauses (toS (rough_state_of (do_cdcl_s_step (state_of (rough_state_of_I S))))) = clauses (toS (rough_state_of_I S))" (is "_ = clauses (toS ?S)")
  by (cases "do_cdcl_s_step (state_of ?S) = state_of ?S")
     (auto dest!: do_cdcl_s_step[of "state_of ?S"] cdcl_s_no_more_clauses)

lemma rough_state_of_I_do_cdcl_s_step'[code abstract]:
 "rough_state_of_I (do_cdcl_s_step' S) =
   rough_state_of (do_cdcl_s_step (id_of_I_to S))"
proof -
  let ?S = "(rough_state_of_I S)"
  have "cdcl_s\<^sup>*\<^sup>* (S0_cdcl (clauses (toS (rough_state_of_I S)))) (toS (rough_state_of_I S))"
    using rough_state_of_I[of S] by auto
  also have "cdcl_s\<^sup>*\<^sup>* (toS (rough_state_of_I S)) (toS (rough_state_of (do_cdcl_s_step (state_of (rough_state_of_I S)))))"
     using do_cdcl_s_step[of "state_of ?S"] 
     by (cases "do_cdcl_s_step (state_of ?S) = state_of ?S") auto
  ultimately show ?thesis
    unfolding do_cdcl_s_step'_def id_of_I_to_def by (auto intro!: state_of_I_inverse)
qed

function do_all_cdcl_s where
"do_all_cdcl_s S =
  (let T = do_cdcl_s_step' S in
  if T = S then S else do_all_cdcl_s T)"
by fast+
termination 
proof (relation "{(T, S). (cdcl_measure (toS (rough_state_of_I T)), cdcl_measure (toS (rough_state_of_I S))) \<in> lexn {(a, b). a < b} 3}", goal_cases)
  case 1
  show ?case by (auto intro!: wf_if_measure_f wf_lexn wf_less)
next
  case (2 S T) note T = this(1) and ST = this(2)
  let ?S = "rough_state_of_I S"
  have S: "cdcl_s\<^sup>*\<^sup>* (S0_cdcl (clauses (toS ?S))) (toS ?S)"
    using rough_state_of_I[of S] by auto
  also have "cdcl_s (toS (rough_state_of_I S)) (toS (rough_state_of_I T))"
    using ST do_cdcl_s_step unfolding T 
    by (smt id_of_I_to_def mem_Collect_eq rough_state_of_I rough_state_of_I_do_cdcl_s_step' rough_state_of_I_inject state_of_inverse)
  moreover 
    have "cdcl_all_inv_mes (toS (rough_state_of_I S))"
      using rough_state_of_I[of S] by auto
    hence "cdcl_all_inv_mes (S0_cdcl (clauses (toS (rough_state_of_I S))))"
      by (cases "rough_state_of_I S")
         (auto simp add: cdcl_all_inv_mes_def distinct_cdcl_state_def)
  ultimately show ?case
    by (auto intro!: cdcl_s_step_decreasing[of _ _ "S0_cdcl (clauses (toS ?S))"] simp del: cdcl_measure.simps simp add: )
qed
   
thm do_all_cdcl_s.induct
lemma do_all_cdcl_s_induct:
  "(\<And>S. (do_cdcl_s_step' S \<noteq> S \<Longrightarrow> P (do_cdcl_s_step' S)) \<Longrightarrow> P S) \<Longrightarrow> P a0"
 using do_all_cdcl_s.induct by metis



lemma no_step_cdcl_s_cdcl_all:
  "no_step cdcl_s (toS (rough_state_of_I (do_all_cdcl_s S)))"
  apply (induction S rule:do_all_cdcl_s_induct)
  apply (case_tac "do_cdcl_s_step' S \<noteq> S")
    apply (metis (mono_tags, hide_lams) do_all_cdcl_s.simps)
  apply (simp add: do_cdcl_s_step'_def id_of_I_to_def)
  by (metis (no_types) do_cdcl_s_step'_def do_cdcl_s_step_no id_of_I_to_def rough_state_of_I_do_cdcl_s_step' rough_state_of_inverse) 
  
lemma do_all_cdcl_s_is_rtranclp_cdcl_s:
  "cdcl_s\<^sup>*\<^sup>* (toS (rough_state_of_I S)) (toS (rough_state_of_I (do_all_cdcl_s S)))"
  apply (induction S rule: do_all_cdcl_s_induct)
  apply (case_tac "do_cdcl_s_step' S = S")
    apply simp
  by (smt converse_rtranclp_into_rtranclp do_all_cdcl_s.simps do_cdcl_s_step id_of_I_to_def rough_state_of_I_do_cdcl_s_step' toS_rough_state_of_state_of_rough_state_of_I)

lemma DPLL_tot_correct:
  assumes r: "rough_state_of_I (do_all_cdcl_s (state_of_I (([], map remdups N, [], 0, C_True)))) = S" and
  S: "(M', N', U', k, E) = toS S"
  shows "(E \<noteq> C_Clause {#} \<and> satisfiable (set (map mset (N)))) 
    \<or> (E = C_Clause {#} \<and> unsatisfiable (set (map mset ( N))))"
proof -
  let ?N = "map remdups N"
  have inv: "cdcl_all_inv_mes (toS ([], map remdups N, [], 0, C_True))"
    unfolding cdcl_all_inv_mes_def distinct_cdcl_state_def distinct_mset_set_def by auto
  hence S0: "rough_state_of (state_of ([], map remdups N, [], 0, C_True)) = ([], map remdups N, [], 0, C_True)" by simp
  have 1: "full0 cdcl_s (toS ([], ?N, [], 0, C_True)) (toS S)"
    unfolding full0_def apply rule
      using do_all_cdcl_s_is_rtranclp_cdcl_s[of "state_of_I ([], map remdups N, [], 0, C_True)"] inv 
        apply (auto simp del: do_all_cdcl_s.simps simp add: state_of_I_inverse r[symmetric])[1]
    using no_step_cdcl_s_cdcl_all r apply blast
    done
  moreover have 2: "finite (set (map mset ?N))" by auto
  moreover have 3: "distinct_mset_set (set (map mset ?N))"
     unfolding distinct_mset_set_def by auto
  moreover 
    have 4: "finite (clauses (S0_cdcl (set (map mset ?N))))"
      by auto
  moreover
    have "cdcl_all_inv_mes (toS S)"
      by (metis (no_types) cdcl_all_inv_mes_rough_state r toS_rough_state_of_state_of_rough_state_of_I)
    hence cons: "consistent_interp (lits_of M')"
      unfolding cdcl_all_inv_mes_def cdcl_M_level_inv_def S[symmetric] by auto
  moreover
    have "clauses (toS ([], ?N, [], 0, C_True)) = clauses (toS S)"
      apply (rule rtranclp_cdcl_no_more_clauses)
      using 1 unfolding full0_def by (auto simp add: rtranclp_cdcl_s_rtranclp_cdcl)
    hence N': "set (map mset ?N) = N'"
      using S by auto
  have "(E \<noteq> C_Clause {#} \<and> satisfiable (set (map mset ?N))) 
    \<or> (E = C_Clause {#} \<and> unsatisfiable (set (map mset ?N)))"
    using full_cdcl_s_normal_forms unfolding N' apply rule
        using 1 apply simp
       using 3 apply simp
      using 2 apply simp
     using cons apply (auto simp add: S[symmetric] true_annots_true_cls)
    done
  thus ?thesis by auto

qed






export_code do_cdcl_s_step' in SML

end
