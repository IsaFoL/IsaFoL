theory CDCL_Implementation
imports DPLL_CDCL_Implementation Propo_CDCL Propo_CDCL_Termination
begin

subsection \<open>CDCL Implementation\<close>
subsubsection \<open>Definition of the rules\<close>
paragraph \<open>Types\<close>
lemma true_clss_remdups[simp]:
  "I \<Turnstile>s (mset \<circ> remdups) ` N \<longleftrightarrow>  I \<Turnstile>s mset ` N"
  by (simp add: true_clss_def)

lemma satisfiable_mset_remdups[simp]:
  "satisfiable ((mset \<circ> remdups) ` N) \<longleftrightarrow> satisfiable (mset ` N)"
unfolding satisfiable_carac[symmetric] by simp

value "backtrack_split [Marked (Pos (Suc 0)) Level]"
value "\<exists>C \<in> set [[Pos (Suc 0), Neg (Suc 0)]]. (\<forall>c \<in> set C. -c \<in> lits_of [Marked (Pos (Suc 0)) Level])"


type_synonym cdcl_state_st = "(nat, nat, nat literal list) marked_lit list \<times> nat literal list list
  \<times> nat literal list list \<times> nat \<times> nat literal list conflicting_clause"
text \<open>We need some functions to convert between our abstract state @{typ "nat cdcl_state"} and the
 concrete state @{typ "cdcl_state_st"}.\<close>

fun convert :: "('a, 'b, 'c list) marked_lit \<Rightarrow> ('a, 'b, 'c multiset) marked_lit"  where
"convert (Propagated L C) = Propagated L (mset C)" |
"convert (Marked K i) = Marked K i"

fun convertC :: "'a list conflicting_clause \<Rightarrow> 'a multiset conflicting_clause"  where
"convertC (C_Clause C) = C_Clause (mset C)" |
"convertC C_True = C_True"

lemma convert_CTrue[iff]:
  "convertC e = C_True \<longleftrightarrow> e = C_True"
  by (cases e) auto

lemma convert_Propagated[elim!]:
  "convert z = Propagated L C \<Longrightarrow> (\<exists>C'. z = Propagated L C' \<and> C = mset C')"
  by (cases z) auto

lemma get_rev_level_map_convert:
  "get_rev_level x n (map convert M) = get_rev_level x n M"
  by (induction M arbitrary: n rule: marked_lit_list_induct) auto

lemma get_level_map_convert[simp]:
  "get_level x (map convert M) = get_level x M"
  using get_rev_level_map_convert[of x 0 "rev M"] by (simp add: rev_map)

lemma get_maximum_level_map_convert[simp]:
  "get_maximum_level D (map convert M) = get_maximum_level D M"
  by (induction D)
     (auto simp add: get_maximum_level_plus)
text \<open>Conversion function\<close>
fun toS :: "cdcl_state_st \<Rightarrow> nat cdcl_state" where
"toS (M, N, U, k, C) = (map convert M, set (map mset N),  set (map mset U), k, convertC C)"

text \<open>Definition an abstract type\<close>
typedef cdcl_state =  "{S::cdcl_state_st. cdcl_all_inv_mes (toS S)}"
  morphisms rough_state_of state_of
proof
  show "([],[], [], 0, C_True) \<in> {S. cdcl_all_inv_mes (toS S)}"
    by (auto simp add: cdcl_all_inv_mes_def)
qed


instantiation cdcl_state :: equal
begin
definition equal_cdcl_state :: "cdcl_state \<Rightarrow> cdcl_state \<Rightarrow> bool" where
 "equal_cdcl_state S S' = (rough_state_of S = rough_state_of S')"
instance
  by standard (simp add: rough_state_of_inject equal_cdcl_state_def)
end

lemma lits_of_map_convert[simp]: "lits_of (map convert M) = lits_of M"
  by (induction M rule: marked_lit_list_induct) simp_all

lemma undefined_lit_map_convert[iff]:
  "undefined_lit L (map convert M) \<longleftrightarrow> undefined_lit L M"
  by (auto simp add: Marked_Propagated_in_iff_in_lits_of)


lemma true_annot_map_convert[simp]: "map convert M \<Turnstile>a N \<longleftrightarrow> M \<Turnstile>a N"
  by (induction M rule: marked_lit_list_induct) (simp_all add: true_annot_def)

lemma true_annots_map_convert[simp]: "map convert M \<Turnstile>as N \<longleftrightarrow> M \<Turnstile>as N"
  unfolding true_annots_def by auto

lemma find_first_unit_clause_some_is_propagate:
  assumes H: "find_first_unit_clause (N @ U) M = Some (L, C)"
  shows "propagate (toS (M, N, U, k, C_True)) (toS (Propagated L C # M, N, U, k, C_True))"
  using assms
  by (auto dest!: find_first_unit_clause_some simp add: propagate.simps
    intro!: exI[of _ "mset C - {#L#}"])

subsubsection \<open>Propagate\<close>
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

  have
    M: "M = map convert ?M" and
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

paragraph \<open>Conflict\<close>
fun find_conflict where
"find_conflict M [] = None" |
"find_conflict M (N # Ns) = (if (\<forall>c \<in> set N. -c \<in> lits_of M) then Some N else find_conflict M Ns)"

lemma find_conflict_Some:
  "find_conflict M Ns = Some N \<Longrightarrow> N \<in> set Ns \<and> M \<Turnstile>as CNot (mset N)"
  by (induction Ns rule: find_conflict.induct)
     (auto split: split_if_asm)

lemma find_conflict_None:
  "find_conflict M Ns = None \<longleftrightarrow> (\<forall>N \<in> set Ns. \<not>M \<Turnstile>as CNot (mset N))"
  by (induction Ns) auto

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
  by (auto dest!:find_conflict_Some split: option.splits)

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
  (do_propagate_step o do_conflict_step) S"

lemma cp_step_is_cdcl_cp:
  assumes H: "do_cp_step S \<noteq> S"
  shows "cdcl_cp (toS S) (toS (do_cp_step S))"
proof -
  show ?thesis
  proof (cases "do_conflict_step S \<noteq> S")
    case True
    thus ?thesis
      by (auto simp add: do_conflict_step do_conflict_step_conflicting do_cp_step_def)
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
        moreover have ns: "no_step conflict (toS S)" using confl do_conflict_step_no_step by blast
        ultimately show ?thesis
          using cdcl_cp.intros(2)[of ?S ?T] confl unfolding do_cp_step_def by auto
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

lemma cdcl_cp_cdcl_st: "cdcl_cp S S' \<Longrightarrow> cdcl\<^sup>*\<^sup>* S S'"
  by (induction rule: cdcl_cp.induct)
     (auto dest!: cdcl.intros)


lemma cdcl_cp_wf: "wf {(S', S::'v Propo_CDCL.cdcl_state). cdcl_all_inv_mes S \<and> cdcl_cp S S'}"
  (is "wf ?R")
proof (rule wf_bounded_measure[of _ "\<lambda>S. card (atms_of_m (clauses S))+1" "\<lambda>S. length (trail S) + (if conflicting S = C_True then 0 else 1)"], goal_cases)
  case (1 S S')
  hence "cdcl_all_inv_mes S" and "cdcl_cp S S'" by auto
  moreover hence "cdcl_all_inv_mes S'" using rtranclp_cdcl_all_inv_mes_inv cdcl_cp_cdcl_st by blast
  ultimately show ?case
    by (auto simp add:cdcl_cp.simps elim!: conflictE propagateE dest: length_model_le_vars_all_inv)
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

paragraph \<open>Skip\<close>
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
     (auto simp add: other split: split_if_asm)

lemma do_skip_step_trail_is_C_True[iff]:
  "do_skip_step S = (a, b, c, d, C_True) \<longleftrightarrow> S = (a, b, c, d, C_True)"
  by (cases S rule: do_skip_step.cases) auto

paragraph \<open>Resolve\<close>
fun maximum_level_code:: "'a literal list \<Rightarrow> ('a, nat, 'a literal list) marked_lit list \<Rightarrow> nat"  where
"maximum_level_code [] _ = 0" |
"maximum_level_code (L # Ls) M = max (get_level L M) (maximum_level_code Ls M)"

lemma maximum_level_code_eq_get_maximum_level[code, simp]:
  "maximum_level_code D M = get_maximum_level (mset D) M"
  by (induction D) (auto simp add: get_maximum_level_plus)

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
    using \<open>- L \<in> set D\<close> by (metis add.commute in_multiset_in_set insert_DiffM)
  have D'L:  "D' + {#- L#} - {#-L#} = D'" by (auto simp add: multiset_eq_iff)

  have CL: "mset C - {#L#} + {#L#} = mset C" using \<open>L \<in> set C\<close> by (auto simp add: multiset_eq_iff)
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
  apply (cases S; cases "hd (trail S)"; cases "conflicting S")
  by (auto
    elim!: resolveE  split: split_if_asm
    dest!: union_single_eq_member
    simp del: in_multiset_in_set get_maximum_level_map_convert
    simp add: in_multiset_in_set[symmetric] get_maximum_level_map_convert[symmetric])


lemma  rough_state_of_state_of_resolve[simp]:
  "cdcl_all_inv_mes (toS S) \<Longrightarrow> rough_state_of (state_of (do_resolve_step S)) = do_resolve_step S"
  apply (rule state_of_inverse)
  by (metis cdcl.simps cdcl_all_inv_mes_inv do_resolve_step resolve mem_Collect_eq)

lemma do_resolve_step_trail_is_C_True[iff]:
  "do_resolve_step S = (a, b, c, d, C_True) \<longleftrightarrow> S = (a, b, c, d, C_True)"
  by (cases S rule: do_resolve_step.cases)
     auto

paragraph \<open>Backjumping\<close>
fun find_level_decomp where
"find_level_decomp M [] D k = None" |
"find_level_decomp M (L # Ls) D k =
  (case (get_level L M, maximum_level_code (D @ Ls) M) of
    (i, j) \<Rightarrow> if i = k \<and> j < i then Some (L, j) else find_level_decomp M Ls (L#D) k
  )"

lemma find_level_decomp_some:
  assumes "find_level_decomp M Ls D k = Some (L, j)"
  shows "L \<in> set Ls \<and> get_maximum_level (mset (remove1 L (Ls @ D))) M = j \<and> get_level L M = k"
  using assms
  apply (induction Ls arbitrary: D)
  apply simp
  apply (auto split: split_if_asm simp add: ac_simps)
  apply (smt ab_semigroup_add_class.add_ac(1) add.commute diff_union_swap mset.simps(2))
  apply (smt add.commute add.left_commute diff_union_cancelL mset.simps(2))
  apply (smt add.commute add.left_commute diff_union_swap mset.simps(2))
  done

lemma find_level_decomp_none:
  assumes "find_level_decomp M Ls E k = None" and "mset (L#D) = mset (Ls @ E)"
  shows "\<not>(L \<in> set Ls \<and> get_maximum_level (mset D) M < k \<and> k = get_level L M)"
  using assms
proof (induction Ls arbitrary: E L D)
  case Nil
  thus ?case by simp
next
  case (Cons L' Ls) note IH = this(1) and find_none = this(2) and LD = this(3)
  have "mset D + {#L'#} = mset E + (mset Ls + {#L'#})  \<Longrightarrow> mset D = mset E + mset Ls"
    by (metis add_right_imp_eq union_assoc)
  thus ?case
    using find_none IH[of "L' # E" L D] LD by (auto simp add: ac_simps split: split_if_asm)
qed

fun bt_cut where
"bt_cut i (Propagated _ _ # Ls) = bt_cut i Ls" |
"bt_cut i (Marked K k # Ls) = (if k = Suc i then Some (Marked K k # Ls) else bt_cut i Ls)" |
"bt_cut i [] = None"

lemma bt_cut_some_decomp:
  "bt_cut i M = Some M' \<Longrightarrow> \<exists>K M2 M1. M = M2 @ M' \<and> M' = Marked K (i+1) # M1"
  by (induction i M rule: bt_cut.induct) (auto split: split_if_asm)

lemma bt_cut_not_none: "M = M2 @ Marked K (Suc i) # M' \<Longrightarrow> bt_cut i M \<noteq> None"
  by (induction M2 arbitrary: M rule: marked_lit_list_induct) auto

lemma get_all_marked_decomposition_ex:
  "\<exists>N. (Marked K (Suc i) # M', N) \<in> set (get_all_marked_decomposition (M2@Marked K (Suc i) # M'))"
  apply (induction M2 rule: marked_lit_list_induct)
    apply auto[2]
  by (case_tac "get_all_marked_decomposition (xs @ Marked K (Suc i) # M')") auto

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
  "(get_all_marked_decomposition (map convert M)) =
    map (\<lambda>(a, b). (map convert a, map convert b)) (get_all_marked_decomposition M)"
  apply (induction M rule: marked_lit_list_induct)
    apply simp
  by (case_tac "get_all_marked_decomposition xs", auto)+

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
      using \<open>L \<in> set C\<close> by (metis add.commute ex_mset in_multiset_in_set insert_DiffM)
    obtain M\<^sub>2 where M\<^sub>2: "bt_cut j M = Some M\<^sub>2"
      using db fd unfolding S E by (auto split: option.splits)
    obtain M1 K where M1: "M\<^sub>2 = Marked K (Suc j) # M1"
      using bt_cut_some_decomp[OF M\<^sub>2] by (cases M\<^sub>2) auto
    obtain c where c: "M = c @ Marked K (Suc j) # M1"
       using bt_cut_in_get_all_marked_decomposition[OF M\<^sub>2]
       unfolding M1 by fastforce
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
    have
      "backtrack
        (map convert M, mset ` set N, mset ` set U, k, C_Clause (mset C))
        (Propagated L (mset C) # map convert M1, mset ` set N, mset ` set U \<union> {mset C}, j, C_True)"
      unfolding C M1 List.list.map set_append
      apply rule
           apply simp
         using Set.imageI[of "(M\<^sub>2, M2)" "set (get_all_marked_decomposition M)"
                             "(\<lambda>(a, b). (map convert a, map convert b))"] M2
         unfolding M1 apply (auto simp add: get_all_marked_decomposition_map_convert)[1]
        using levL apply simp
       using max_l_j levL \<open>j \<le> k\<close> apply (simp add: get_maximum_level_plus)
      using max_l_j by simp
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
  thus ?case using db by (auto split: option.splits elim!: backtrackE)
next
  case (2 M N U k E C) note bt = this(1) and S = this(2) and confl = this(3)
  obtain D L K b z M1 j where
    levL: "get_level L M = get_maximum_level (D + {#L#}) M" and
    k: "k = get_maximum_level (D + {#L#}) M" and
    j: "j = get_maximum_level D M" and
    CE: "convertC E = C_Clause (D + {#L#})" and
    decomp: "(z # M1, b) \<in> set (get_all_marked_decomposition M)" and
    z: "Marked K (Suc j) = convert z" using bt unfolding S
      by (auto split: option.splits elim!: backtrackE
        simp add: get_all_marked_decomposition_map_convert)
  have z: "z = Marked K (Suc j)" using z by (cases z) auto
  obtain c where c: "M = c @ b @ Marked K (Suc j) # M1"
    using decomp unfolding z by blast
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
    using C \<open>k > j\<close> mset_eq_setD unfolding k[symmetric] D'D j[symmetric] levL by fastforce+
  then obtain L' j' where fd_some: "find_level_decomp M C [] k = Some (L', j')"
    by (cases "find_level_decomp M C [] k") auto
  have L': "L' = L"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "L' \<in># D"
        by (metis C D'D fd_some find_level_decomp_some in_multiset_in_set insert_iff list.simps(15))
      hence "get_level L' M \<le> get_maximum_level D M"
        using get_maximum_level_ge_get_level by blast
      thus False using \<open>k > j\<close> j find_level_decomp_some[OF fd_some] by auto
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

lemma rough_state_of_state_of_backtrack[simp]:
  assumes "cdcl_all_inv_mes (toS S)"
  shows "rough_state_of (state_of (do_backtrack_step S))= do_backtrack_step S"
  apply (rule state_of_inverse)
  using assms by (metis cdcl.simps cdcl_all_inv_mes_inv do_backtrack_step backtrack mem_Collect_eq)

paragraph \<open>Decide\<close>
fun do_decide_step where
"do_decide_step (M, N, U, k, C_True) =
  (case find_first_unused_var N (lits_of M) of
    None \<Rightarrow> (M, N, U, k, C_True)
  | Some L \<Rightarrow> (Marked L (Suc k) # M, N, U, k+1, C_True))" |
"do_decide_step S = S"

lemma do_decide_step:
  "do_decide_step S \<noteq> S \<Longrightarrow> decided (toS S) (toS (do_decide_step S))"
  apply (cases S, cases "conflicting S")
  defer
  apply (auto split: option.splits simp add:  decided.simps Marked_Propagated_in_iff_in_lits_of
          dest: find_first_unused_var_undefined find_first_unused_var_Some
          intro: atms_of_atms_of_m_mono)[1]
proof -
  fix a b c d e
  {
    fix a :: "(nat, nat, nat literal list) marked_lit list" and
        b :: "nat literal list list" and  c :: "nat literal list list" and
        d :: nat and x2 :: "nat literal" and m :: "nat literal list"
    assume a1: "m \<in> set b"
    assume "x2 \<in> set m"
    hence f2: "atm_of x2 \<in> atms_of (mset m)"
      by simp
    have "\<And>f. (f m::nat literal multiset) \<in> f ` set b"
      using a1 by blast
    hence "\<And>f. (atms_of (f m)::nat set) \<subseteq> atms_of_m (f ` set b)"
     using atms_of_atms_of_m_mono by blast
    hence "\<And>n f. (n::nat) \<in> atms_of_m (f ` set b) \<or> n \<notin> atms_of (f m)"
      by (meson contra_subsetD)
    hence "atm_of x2 \<in> atms_of_m (mset ` set b)"
      using f2 by blast
  } note H = this
  assume  "do_decide_step S \<noteq> S" and
     "S = (a, b, c, d, e)" and
     "conflicting S = C_True"
  then show "decided (toS S) (toS (do_decide_step S))"
  (* TODO tune proof *)
    apply (auto split: option.splits simp add: decided.simps Marked_Propagated_in_iff_in_lits_of
             dest!: find_first_unused_var_Some dest: H)
    by (meson atm_of_in_atm_of_set_in_uminus contra_subsetD rev_image_eqI)+
qed


lemma do_decide_step_no:
  "do_decide_step S = S \<Longrightarrow> no_step decided (toS S)"
  by (cases S, cases "conflicting S")
    (fastforce
      simp add: atms_of_m_mset_unfold atm_of_eq_atm_of Marked_Propagated_in_iff_in_lits_of
      split: option.splits)+

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

subsubsection \<open>Code generation\<close>
paragraph \<open>Type definition\<close>
text \<open>There are two invariants: one while applying conflict and propagate and one for the other
 rules\<close>
thm rough_state_of_inverse[simp add]
definition Con  where
  "Con xs = state_of (if cdcl_all_inv_mes (toS (fst xs, snd xs)) then xs else ([], [], [], 0, C_True))"

lemma [code abstype]:
 "Con (rough_state_of S) = S"
  using rough_state_of[of S] unfolding Con_def by (simp add: rough_state_of_inverse)

definition do_cp_step' where
"do_cp_step' S = state_of (do_cp_step (rough_state_of S))"

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

paragraph \<open>Conflict and Propagate\<close>
function do_full_cp_step :: "cdcl_state \<Rightarrow> cdcl_state" where
"do_full_cp_step S =
  (let S' = do_cp_step' S in
   if S = S' then S else do_full_cp_step S')"
by auto
termination
proof (relation "{(T', T). (rough_state_of T', rough_state_of T) \<in> {(S', S).
  (toS S', toS S) \<in> {(S', S). cdcl_all_inv_mes S \<and> cdcl_cp S S'}}}", goal_cases)
  case 1
  show ?case
    using wf_if_measure_f[OF wf_if_measure_f[OF cdcl_cp_wf, of "toS"], of rough_state_of] .
next
  case 2
  thus ?case
    using rough_state_of unfolding do_cp_step'_def by (metis (no_types, lifting) case_prodI
      cp_step_is_cdcl_cp mem_Collect_eq rough_state_of_inject rough_state_of_state_of_do_cp_step)
qed

lemma do_full_cp_step_fix_point_of_do_full_cp_step:
  "do_cp_step(rough_state_of (do_full_cp_step S)) = (rough_state_of (do_full_cp_step S))"
 by (rule do_full_cp_step.induct[of "\<lambda>S. do_cp_step(rough_state_of (do_full_cp_step S)) = (rough_state_of (do_full_cp_step S))"])
    (metis (full_types) do_full_cp_step.elims rough_state_of_state_of_do_cp_step do_cp_step'_def)

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

paragraph \<open>The other rules\<close>
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

definition do_cdcl_s_step' where
"do_cdcl_s_step' S = state_of_I (rough_state_of (do_cdcl_s_step (id_of_I_to S)))"

lemma toS_do_full_cp_step_not_eq: "do_full_cp_step S \<noteq> S \<Longrightarrow>
    toS (rough_state_of S) \<noteq> toS (rough_state_of (do_full_cp_step S))"
  by (metis (mono_tags, lifting) cp_step_is_cdcl_cp do_cp_step'_def do_full_cp_step.simps
  do_full_cp_step_full0 full0_def rough_state_of_inverse)

text \<open>@{term do_full_cp_step} should not be unfolded anymore:\<close>
declare do_full_cp_step.simps[simp del]

paragraph \<open>Correction of the transformation\<close>
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
  moreover
    have
      np: "no_step propagate (toS (rough_state_of S))" and
      nc: "no_step conflict (toS (rough_state_of S))"
      by (metis True do_cp_step_eq_no_step do_full_cp_step_fix_point_of_do_full_cp_step
       in_clauses_rough_state_of_is_distinct no_cdcl_cp_iff_no_propagate_no_conflict)+
    hence "no_step cdcl_cp (toS (rough_state_of S))"
      by (meson cdcl_cp.cases)
  moreover have "cdcl_cp\<^sup>\<down> (toS (rough_state_of (do_other_step' S)))
    (toS (rough_state_of (do_full_cp_step (do_other_step' S))))"
    using do_full_cp_step_full0 by auto
  ultimately show ?thesis
    using assms True unfolding do_cdcl_s_step_def
    by (auto intro!: cdcl_s.other' dest: toS_do_full_cp_step_not_eq)
qed

lemma length_trail_toS[simp]:
  "length (trail (toS S)) = length (trail S)"
  by (cases S) auto

lemma conflicting_noTrue_iff_toS[simp]:
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
          trail_toS_neq_imp_trail_neq)[3]
    by (elim backtrackE) (smt backtrackE get_all_marked_decomposition_exists_prepend append_Cons
      append_Nil2 append_assoc list.inject marked_lit.distinct(1) rev_append rev_eq_Cons_iff
      same_append_eq trail_conv trail_toS_neq_imp_trail_neq)
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
  by (smt Un_iff append_assoc do_cp_step'_def do_cp_step_neq_trail_increase do_full_cp_step.simps
    rough_state_of_state_of_do_cp_step set_append)

lemma do_cp_step_conflicting:
  "conflicting (rough_state_of S) \<noteq> C_True \<Longrightarrow> do_cp_step' S = S"
  unfolding do_cp_step'_def do_cp_step_def by (simp add: rough_state_of_inverse)

lemma do_full_cp_step_conflicting:
  "conflicting (rough_state_of S) \<noteq> C_True \<Longrightarrow> do_full_cp_step S = S"
  unfolding do_cp_step'_def do_cp_step_def
  apply (induction rule: do_full_cp_step_induct)
  by (case_tac "S \<noteq> do_cp_step' S")
     (auto simp add: rough_state_of_inverse do_full_cp_step.simps dest: do_cp_step_conflicting)

lemma do_decide_step_not_conflicting_one_more_decide:
  assumes
    "conflicting S = C_True" and
    "do_decide_step S \<noteq> S"
    shows "Suc (length (filter is_marked (trail S))) = length (filter is_marked (trail (do_decide_step S)))"
  using assms unfolding do_other_step'_def
  by (cases S) (auto simp add: rough_state_of_inverse Let_def split: split_if_asm option.splits
     dest!: find_first_unused_var_Some_not_all_incl)

lemma do_decide_step_not_conflicting_one_more_decide_bt:
  assumes "conflicting S \<noteq> C_True" and
  "do_decide_step S \<noteq> S"
  shows "length (filter is_marked (trail S)) < length (filter is_marked (trail (do_decide_step S)))"
  using assms unfolding do_other_step'_def by (cases S, cases "conflicting S")
    (auto simp add: rough_state_of_inverse Let_def split: split_if_asm option.splits)

lemma do_other_step_not_conflicting_one_more_decide_bt:
  assumes "conflicting (rough_state_of S) \<noteq> C_True" and
  "conflicting (rough_state_of (do_other_step' S)) = C_True" and
  "do_other_step' S \<noteq> S"
  shows "length (filter is_marked (trail (rough_state_of S)))
    > length (filter is_marked (trail (rough_state_of (do_other_step' S))))"
proof (cases S, goal_cases)
  case (1 y) note S = this(1) and inv = this(2)
  obtain M N U k E where y: "y = (M, N, U, k, C_Clause E)"
    using assms(1) S inv by (cases y, cases "conflicting y") auto
  have M: "rough_state_of (state_of (M, N, U, k,  C_Clause E)) = (M, N, U, k,  C_Clause E)"
    using inv y by (auto simp add: state_of_inverse)
  have bt: "do_other_step' S = state_of (do_backtrack_step (rough_state_of S))"
  (* TODO tune proof *)
    using assms(1,2) apply (cases "rough_state_of (do_other_step' S)")
      apply(auto simp add: Let_def do_other_step'_def)
    apply (cases "rough_state_of S" rule: do_decide_step.cases)
    apply auto
    done
  show ?case
    using assms(2) S unfolding bt y inv
    apply simp
    by (auto simp add: M
          split: option.splits
          dest: bt_cut_some_decomp arg_cong[of _ _ "\<lambda>u. length (filter is_marked u)"])
qed


lemma do_other_step_not_conflicting_one_more_decide:
  assumes "conflicting (rough_state_of S) = C_True" and
  "do_other_step' S \<noteq> S"
  shows "1 + length (filter is_marked (trail (rough_state_of S)))
    = length (filter is_marked (trail (rough_state_of (do_other_step' S))))"
proof (cases S, goal_cases)
  case (1 y) note S = this(1) and inv = this(2)
  obtain M N U k where y: "y = (M, N, U, k, C_True)" using assms(1) S inv by (cases y) auto
  have M: "rough_state_of (state_of (M, N, U, k, C_True)) = (M, N, U, k, C_True)"
    using inv y by (auto simp add: state_of_inverse)
  have "state_of (do_decide_step (M, N, U, k, C_True)) \<noteq> state_of (M, N, U, k, C_True)"
    using assms(2) unfolding do_other_step'_def y inv S by (auto simp add: M)
  hence f4: "do_skip_step (rough_state_of S) = rough_state_of S"
    unfolding S M y by (metis (full_types) do_skip_step.simps(4))
  have f5: "do_resolve_step (rough_state_of S) = rough_state_of S"
    unfolding S M y by (metis (no_types) do_resolve_step.simps(4))
  have f6: "do_backtrack_step (rough_state_of S) = rough_state_of S"
    unfolding S M y by (metis (no_types) do_backtrack_step.simps(2))
  have "do_other_step (rough_state_of S) \<noteq> rough_state_of S"
    using assms(2) unfolding S M y do_other_step'_def by (metis (no_types))
  thus ?case
    using f6 f5 f4 by (simp add: assms(1) do_decide_step_not_conflicting_one_more_decide
      do_other_step'_def)
qed

lemma rough_state_of_state_of_do_skip_step_rough_state_of[simp]:
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

lemma do_skip_step_eq_iff_trail_eq:
  "do_skip_step S = S \<longleftrightarrow> trail (do_skip_step S) = trail S"
  by (cases S rule: do_skip_step.cases) auto

lemma do_decide_step_eq_iff_trail_eq:
  "do_decide_step S = S \<longleftrightarrow> trail (do_decide_step S) = trail S"
  by (cases S rule: do_decide_step.cases) (auto split: option.split)

lemma do_backtrack_step_eq_iff_trail_eq:
  "do_backtrack_step S = S \<longleftrightarrow> trail (do_backtrack_step S) = trail S"
  by (cases S rule: do_backtrack_step.cases)
     (auto split: option.split list.splits marked_lit.splits
       dest!: bt_cut_in_get_all_marked_decomposition)

lemma do_resolve_step_eq_iff_trail_eq:
  "do_resolve_step S = S \<longleftrightarrow> trail (do_resolve_step S) = trail S"
  by (cases S rule: do_resolve_step.cases) auto

lemma do_other_step_eq_iff_trail_eq:
  "trail (do_other_step S) = trail S \<longleftrightarrow> do_other_step S = S"
  by (auto simp add: Let_def do_skip_step_eq_iff_trail_eq[symmetric]
    do_decide_step_eq_iff_trail_eq[symmetric] do_backtrack_step_eq_iff_trail_eq[symmetric]
    do_resolve_step_eq_iff_trail_eq[symmetric])


lemma do_full_cp_step_do_other_step'_normal_form[dest!]:
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
      by (simp add: do_other_step_eq_iff_trail_eq do_other_step'_def rough_state_of_inverse
        del: do_other_step.simps)
  }
  moreover {
    assume eq[simp]: "do_other_step' S = S"
    obtain c where c: "trail (rough_state_of (do_full_cp_step S)) = c @ trail (rough_state_of S)"
      using do_full_cp_step_neq_trail_increase by auto

    moreover have "trail (rough_state_of (do_full_cp_step S)) = trail (rough_state_of S)"
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
    have "length (filter is_marked (trail (rough_state_of (do_full_cp_step ?T))))
       = length (filter is_marked (trail (rough_state_of ?T)))" using nm unfolding c by force
    moreover have "length (filter is_marked (trail (rough_state_of S)))
       \<noteq> length (filter is_marked  (trail (rough_state_of ?T)))"
      using do_other_step_not_conflicting_one_more_decide[OF _ neq]
      do_other_step_not_conflicting_one_more_decide_bt[of S, OF _ confl neq]
      by linarith
    finally have False unfolding H by blast
  }
  ultimately show ?thesis by blast
qed

lemma do_cdcl_s_step_no:
  assumes S: "do_cdcl_s_step S = S"
  shows "no_step cdcl_s (toS (rough_state_of S))"
proof -
  {
    fix S'
    assume "full cdcl_cp (toS (rough_state_of S)) S'"
    hence False
      using do_full_cp_step_full0[of S] unfolding full0_def S rtranclp_unfold full_def
      by (metis (mono_tags, lifting) assms do_cdcl_s_step_def tranclpD)
  }
  moreover {
    fix S' S''
    assume " cdcl_o (toS (rough_state_of S)) S'" and
     "no_step propagate (toS (rough_state_of S))" and
     "no_step conflict (toS (rough_state_of S))" and
     "cdcl_cp\<^sup>\<down> S' S''"
    hence False
      using assms unfolding do_cdcl_s_step_def by (metis (full_types) cdcl_all_inv_mes_rough_state
        do_full_cp_step_do_other_step'_normal_form do_other_step_no rough_state_of_do_other_step')
  }
  ultimately show ?thesis using assms by (meson cdcl_cp.simps cdcl_s.cases)
qed

lemma toS_rough_state_of_state_of_rough_state_of_I[simp]:
  "toS (rough_state_of (state_of (rough_state_of_I S))) = toS (rough_state_of_I S)"
  using rough_state_of_I[of S] by (auto simp add: state_of_inverse)

lemma clauses_toS_rough_state_of_do_cdcl_s_step[simp]:
  "clauses (toS (rough_state_of (do_cdcl_s_step (state_of (rough_state_of_I S)))))
    = clauses (toS (rough_state_of_I S))" (is "_ = clauses (toS ?S)")
  by (cases "do_cdcl_s_step (state_of ?S) = state_of ?S")
     (auto dest!: do_cdcl_s_step[of "state_of ?S"] cdcl_s_no_more_clauses)

lemma rough_state_of_I_do_cdcl_s_step'[code abstract]:
 "rough_state_of_I (do_cdcl_s_step' S) =
   rough_state_of (do_cdcl_s_step (id_of_I_to S))"
proof -
  let ?S = "(rough_state_of_I S)"
  have "cdcl_s\<^sup>*\<^sup>* (S0_cdcl (clauses (toS (rough_state_of_I S)))) (toS (rough_state_of_I S))"
    using rough_state_of_I[of S] by auto
  moreover have "cdcl_s\<^sup>*\<^sup>*
                  (toS (rough_state_of_I S))
                  (toS (rough_state_of (do_cdcl_s_step (state_of (rough_state_of_I S)))))"
     using do_cdcl_s_step[of "state_of ?S"]
     by (cases "do_cdcl_s_step (state_of ?S) = state_of ?S") auto
  ultimately show ?thesis
    unfolding do_cdcl_s_step'_def id_of_I_to_def by (auto intro!: state_of_I_inverse)
qed

paragraph \<open>All rules together\<close>
function do_all_cdcl_s where
"do_all_cdcl_s S =
  (let T = do_cdcl_s_step' S in
  if T = S then S else do_all_cdcl_s T)"
by fast+
termination
proof (relation "{(T, S).
    (cdcl_measure (toS (rough_state_of_I T)), cdcl_measure (toS (rough_state_of_I S)))
      \<in> lexn {(a, b). a < b} 3}", goal_cases)
  case 1
  show ?case by (auto intro!: wf_if_measure_f wf_lexn wf_less)
next
  case (2 S T) note T = this(1) and ST = this(2)
  let ?S = "rough_state_of_I S"
  have S: "cdcl_s\<^sup>*\<^sup>* (S0_cdcl (clauses (toS ?S))) (toS ?S)"
    using rough_state_of_I[of S] by auto
  moreover have "cdcl_s (toS (rough_state_of_I S)) (toS (rough_state_of_I T))"
    using ST do_cdcl_s_step unfolding T
    by (smt id_of_I_to_def mem_Collect_eq rough_state_of_I rough_state_of_I_do_cdcl_s_step'
      rough_state_of_I_inject state_of_inverse)
  moreover
    have "cdcl_all_inv_mes (toS (rough_state_of_I S))"
      using rough_state_of_I[of S] by auto
    hence "cdcl_all_inv_mes (S0_cdcl (clauses (toS (rough_state_of_I S))))"
      by (cases "rough_state_of_I S")
         (auto simp add: cdcl_all_inv_mes_def distinct_cdcl_state_def)
  ultimately show ?case
    by (auto intro!: cdcl_s_step_decreasing[of _ _ "S0_cdcl (clauses (toS ?S))"]
      simp del: cdcl_measure.simps)
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
  by (metis (full_types) do_all_cdcl_s.simps do_cdcl_s_step_no id_of_I_to_def
    rough_state_of_I_do_cdcl_s_step' rough_state_of_inverse)


lemma do_all_cdcl_s_is_rtranclp_cdcl_s:
  "cdcl_s\<^sup>*\<^sup>* (toS (rough_state_of_I S)) (toS (rough_state_of_I (do_all_cdcl_s S)))"
  apply (induction S rule: do_all_cdcl_s_induct)
  apply (case_tac "do_cdcl_s_step' S = S")
    apply simp
  by (smt converse_rtranclp_into_rtranclp do_all_cdcl_s.simps do_cdcl_s_step id_of_I_to_def
    rough_state_of_I_do_cdcl_s_step' toS_rough_state_of_state_of_rough_state_of_I)

text \<open>Final theorem:\<close>
lemma DPLL_tot_correct:
  assumes
    r: "rough_state_of_I (do_all_cdcl_s (state_of_I (([], map remdups N, [], 0, C_True)))) = S" and
    S: "(M', N', U', k, E) = toS S"
  shows "(E \<noteq> C_Clause {#} \<and> satisfiable (set (map mset (N))))
    \<or> (E = C_Clause {#} \<and> unsatisfiable (set (map mset ( N))))"
proof -
  let ?N = "map remdups N"
  have inv: "cdcl_all_inv_mes (toS ([], map remdups N, [], 0, C_True))"
    unfolding cdcl_all_inv_mes_def distinct_cdcl_state_def distinct_mset_set_def by auto
  hence S0: "rough_state_of (state_of ([], map remdups N, [], 0, C_True))
    = ([], map remdups N, [], 0, C_True)" by simp
  have 1: "full0 cdcl_s (toS ([], ?N, [], 0, C_True)) (toS S)"
    unfolding full0_def apply rule
      using do_all_cdcl_s_is_rtranclp_cdcl_s[of "state_of_I ([], map remdups N, [], 0, C_True)"] inv
        no_step_cdcl_s_cdcl_all
        by (auto simp del: do_all_cdcl_s.simps simp add: state_of_I_inverse r[symmetric])+
  moreover have 2: "finite (set (map mset ?N))" by auto
  moreover have 3: "distinct_mset_set (set (map mset ?N))"
     unfolding distinct_mset_set_def by auto
  moreover
    have 4: "finite (clauses (S0_cdcl (set (map mset ?N))))"
      by auto
  moreover
    have "cdcl_all_inv_mes (toS S)"
      by (metis (no_types) cdcl_all_inv_mes_rough_state r
        toS_rough_state_of_state_of_rough_state_of_I)
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
     using 1 2 3 cons by (auto simp add: S[symmetric] true_annots_true_cls)
  thus ?thesis by auto
qed

paragraph \<open>The Code\<close>
text \<open>The SML code is skipped in the documentation, but stays to ensure that some version of the
 exported code is working\<close>
(*<*)
fun gene where
"gene 0 = [[Pos 0], [Neg 0]]" |
"gene (Suc n) = map (op # (Pos (Suc n))) (gene n) @ map (op # (Neg (Suc n))) (gene n)"

value "gene 1"

export_code do_all_cdcl_s gene in OCaml
ML \<open>
structure HOL : sig
  type 'a equal
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

end; (*struct HOL*)

structure List : sig
  val equal_list : 'a HOL.equal -> ('a list) HOL.equal
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev : 'a list -> 'a list
  val find : ('a -> bool) -> 'a list -> 'a option
  val null : 'a list -> bool
  val filter : ('a -> bool) -> 'a list -> 'a list
  val member : 'a HOL.equal -> 'a list -> 'a -> bool
  val remdups : 'a HOL.equal -> 'a list -> 'a list
  val remove1 : 'a HOL.equal -> 'a -> 'a list -> 'a list
  val map : ('a -> 'b) -> 'a list -> 'b list
  val pred_list : ('a -> bool) -> 'a list -> bool
end = struct

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    HOL.eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) HOL.equal;

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun find uu [] = NONE
  | find p (x :: xs) = (if p x then SOME x else find p xs);

fun null [] = true
  | null (x :: xs) = false;

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun member A_ [] y = false
  | member A_ (x :: xs) y = HOL.eq A_ x y orelse member A_ xs y;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if member A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun remove1 A_ x [] = []
  | remove1 A_ x (y :: xs) =
    (if HOL.eq A_ x y then xs else y :: remove1 A_ x xs);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun pred_list p [] = true
  | pred_list p (x :: xs) = p x andalso pred_list p xs;

end; (*struct List*)

structure Set : sig
  datatype 'a set = Set of 'a list | Coset of 'a list
  val image : ('a -> 'b) -> 'a set -> 'b set
  val member : 'a HOL.equal -> 'a -> 'a set -> bool
end = struct

datatype 'a set = Set of 'a list | Coset of 'a list;

fun image f (Set xs) = Set (List.map f xs);

fun member A_ x (Coset xs) = not (List.member A_ xs x)
  | member A_ x (Set xs) = List.member A_ xs x;

end; (*struct Set*)

structure Orderings : sig
  type 'a ord
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  type 'a preorder
  val ord_preorder : 'a preorder -> 'a ord
  type 'a order
  val preorder_order : 'a order -> 'a preorder
  type 'a linorder
  val order_linorder : 'a linorder -> 'a order
  val max : 'a ord -> 'a -> 'a -> 'a
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

fun max A_ a b = (if less_eq A_ a b then b else a);

end; (*struct Orderings*)

structure Arith : sig
  datatype nat = Nat of IntInf.int;
  val equal_nata : nat -> nat -> bool
  val equal_nat : nat HOL.equal
  val less_nat : nat -> nat -> bool
  val linorder_nat : nat Orderings.linorder
  type num
  val plus_nat : nat -> nat -> nat
  val one_nat : nat
  val suc : nat -> nat
  val zero_nat : nat
  val minus_nat : nat -> nat -> nat
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val equal_nat = {equal = equal_nata} : nat HOL.equal;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat Orderings.ord;

val preorder_nat = {ord_preorder = ord_nat} : nat Orderings.preorder;

val order_nat = {preorder_order = preorder_nat} : nat Orderings.order;

val linorder_nat = {order_linorder = order_nat} : nat Orderings.linorder;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int Orderings.ord;

datatype num = One | Bit0 of num | Bit1 of num;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

val zero_nat : nat = Nat (0 : IntInf.int);

fun minus_nat m n =
  Nat (Orderings.max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

end; (*struct Arith*)

structure Multiset : sig
  datatype 'a multiset = Mset of 'a list
  val single : 'a -> 'a multiset
  val set_mset : 'a multiset -> 'a Set.set
  val image_mset : ('a -> 'b) -> 'a multiset -> 'b multiset
  val plus_multiset : 'a multiset -> 'a multiset -> 'a multiset
end = struct

datatype 'a multiset = Mset of 'a list;

fun single x = Mset [x];

fun set_mset (Mset x) = Set.Set x;

fun image_mset f (Mset xs) = Mset (List.map f xs);

fun plus_multiset (Mset xs) (Mset ys) = Mset (xs @ ys);

end; (*struct Multiset*)

structure Clausal_Logic : sig
  datatype 'a literal = Pos of 'a | Neg of 'a
  val equal_literala : 'a HOL.equal -> 'a literal -> 'a literal -> bool
  val equal_literal : 'a HOL.equal -> 'a literal HOL.equal
  val atm_of : 'a literal -> 'a
  val uminus_literal : 'a literal -> 'a literal
end = struct

datatype 'a literal = Pos of 'a | Neg of 'a;

fun equal_literala A_ (Pos x1) (Neg x2) = false
  | equal_literala A_ (Neg x2) (Pos x1) = false
  | equal_literala A_ (Neg x2) (Neg y2) = HOL.eq A_ x2 y2
  | equal_literala A_ (Pos x1) (Pos y1) = HOL.eq A_ x1 y1;

fun equal_literal A_ = {equal = equal_literala A_} : 'a literal HOL.equal;

fun atm_of (Pos x1) = x1
  | atm_of (Neg x2) = x2;

fun is_pos (Pos x1) = true
  | is_pos (Neg x2) = false;

fun uminus_literal l = (if is_pos l then Neg else Pos) (atm_of l);

end; (*struct Clausal_Logic*)

structure Partial_Annotated_Clausal_Logic : sig
  datatype ('a, 'b, 'c) marked_lit = Marked of 'a Clausal_Logic.literal * 'b |
    Propagated of 'a Clausal_Logic.literal * 'c
  val equal_marked_lit :
    'a HOL.equal -> 'b HOL.equal -> 'c HOL.equal ->
      ('a, 'b, 'c) marked_lit HOL.equal
  val lits_of : ('a, 'b, 'c) marked_lit list -> 'a Clausal_Logic.literal Set.set
end = struct

datatype ('a, 'b, 'c) marked_lit = Marked of 'a Clausal_Logic.literal * 'b |
  Propagated of 'a Clausal_Logic.literal * 'c;

fun equal_marked_lita A_ B_ C_ (Marked (x11, x12)) (Propagated (x21, x22)) =
  false
  | equal_marked_lita A_ B_ C_ (Propagated (x21, x22)) (Marked (x11, x12)) =
    false
  | equal_marked_lita A_ B_ C_ (Propagated (x21, x22)) (Propagated (y21, y22)) =
    Clausal_Logic.equal_literala A_ x21 y21 andalso HOL.eq C_ x22 y22
  | equal_marked_lita A_ B_ C_ (Marked (x11, x12)) (Marked (y11, y12)) =
    Clausal_Logic.equal_literala A_ x11 y11 andalso HOL.eq B_ x12 y12;

fun equal_marked_lit A_ B_ C_ = {equal = equal_marked_lita A_ B_ C_} :
  ('a, 'b, 'c) marked_lit HOL.equal;

fun lit_of (Marked (x11, x12)) = x11
  | lit_of (Propagated (x21, x22)) = x21;

fun lits_of ls = Set.image lit_of (Set.Set ls);

end; (*struct Partial_Annotated_Clausal_Logic*)

structure Lattices_Big : sig
  val max : 'a Orderings.linorder -> 'a Set.set -> 'a
end = struct

fun max A_ (Set.Set (x :: xs)) =
  List.fold
    (Orderings.max
      ((Orderings.ord_preorder o Orderings.preorder_order o
         Orderings.order_linorder)
        A_))
    xs x;

end; (*struct Lattices_Big*)

structure Propo_CDCL : sig
  datatype 'a conflicting_clause = C_True | C_Clause of 'a
  val equal_conflicting_clause : 'a HOL.equal -> 'a conflicting_clause HOL.equal
  val get_rev_level :
    'a HOL.equal ->
      'a Clausal_Logic.literal ->
        Arith.nat ->
          ('a, Arith.nat, 'b) Partial_Annotated_Clausal_Logic.marked_lit list ->
            Arith.nat
  val get_maximum_level :
    'a HOL.equal ->
      'a Clausal_Logic.literal Multiset.multiset ->
        ('a, Arith.nat, 'b) Partial_Annotated_Clausal_Logic.marked_lit list ->
          Arith.nat
end = struct

datatype 'a conflicting_clause = C_True | C_Clause of 'a;

fun equal_conflicting_clausea A_ C_True (C_Clause x2) = false
  | equal_conflicting_clausea A_ (C_Clause x2) C_True = false
  | equal_conflicting_clausea A_ (C_Clause x2) (C_Clause y2) = HOL.eq A_ x2 y2
  | equal_conflicting_clausea A_ C_True C_True = true;

fun equal_conflicting_clause A_ = {equal = equal_conflicting_clausea A_} :
  'a conflicting_clause HOL.equal;

fun get_rev_level A_ uu uv [] = Arith.zero_nat
  | get_rev_level A_ la n
    (Partial_Annotated_Clausal_Logic.Marked (l, level) :: ls) =
    (if HOL.eq A_ (Clausal_Logic.atm_of l) (Clausal_Logic.atm_of la) then level
      else get_rev_level A_ la level ls)
  | get_rev_level A_ la n
    (Partial_Annotated_Clausal_Logic.Propagated (l, uw) :: ls) =
    (if HOL.eq A_ (Clausal_Logic.atm_of l) (Clausal_Logic.atm_of la) then n
      else get_rev_level A_ la n ls);

fun get_maximum_level A_ d m =
  Lattices_Big.max Arith.linorder_nat
    (Multiset.set_mset
      (Multiset.plus_multiset (Multiset.single Arith.zero_nat)
        (Multiset.image_mset
          (fn l => get_rev_level A_ l Arith.zero_nat (List.rev m)) d)));

end; (*struct Propo_CDCL*)

structure Product_Type : sig
  val equal_proda : 'a HOL.equal -> 'b HOL.equal -> 'a * 'b -> 'a * 'b -> bool
  val equal_prod : 'a HOL.equal -> 'b HOL.equal -> ('a * 'b) HOL.equal
end = struct

fun equal_proda A_ B_ (x1, x2) (y1, y2) =
  HOL.eq A_ x1 y1 andalso HOL.eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) HOL.equal;

end; (*struct Product_Type*)

structure CDCL_Implementation : sig
  datatype cdcl_state_I =
  ConI of
    ((Arith.nat, Arith.nat, (Arith.nat Clausal_Logic.literal list))
       Partial_Annotated_Clausal_Logic.marked_lit list *
      ((Arith.nat Clausal_Logic.literal list) list *
        ((Arith.nat Clausal_Logic.literal list) list *
          (Arith.nat *
            (Arith.nat Clausal_Logic.literal list)
              Propo_CDCL.conflicting_clause))));
  val gene : Arith.nat -> (Arith.nat Clausal_Logic.literal list) list
  val do_all_cdcl_s : cdcl_state_I -> cdcl_state_I
end = struct

datatype cdcl_state =
  Con of
    ((Arith.nat, Arith.nat, (Arith.nat Clausal_Logic.literal list))
       Partial_Annotated_Clausal_Logic.marked_lit list *
      ((Arith.nat Clausal_Logic.literal list) list *
        ((Arith.nat Clausal_Logic.literal list) list *
          (Arith.nat *
            (Arith.nat Clausal_Logic.literal list)
              Propo_CDCL.conflicting_clause))));

datatype cdcl_state_I =
  ConI of
    ((Arith.nat, Arith.nat, (Arith.nat Clausal_Logic.literal list))
       Partial_Annotated_Clausal_Logic.marked_lit list *
      ((Arith.nat Clausal_Logic.literal list) list *
        ((Arith.nat Clausal_Logic.literal list) list *
          (Arith.nat *
            (Arith.nat Clausal_Logic.literal list)
              Propo_CDCL.conflicting_clause))));

fun gene n =
  (if Arith.equal_nata n Arith.zero_nat
    then [[Clausal_Logic.Pos Arith.zero_nat],
           [Clausal_Logic.Neg Arith.zero_nat]]
    else List.map
           (fn a =>
             Clausal_Logic.Pos (Arith.suc (Arith.minus_nat n Arith.one_nat)) ::
               a)
           (gene (Arith.minus_nat n Arith.one_nat)) @
           List.map
             (fn a =>
               Clausal_Logic.Neg
                 (Arith.suc (Arith.minus_nat n Arith.one_nat)) ::
                 a)
             (gene (Arith.minus_nat n Arith.one_nat)));

fun bt_cut i (Partial_Annotated_Clausal_Logic.Propagated (uu, uv) :: ls) =
  bt_cut i ls
  | bt_cut i (Partial_Annotated_Clausal_Logic.Marked (ka, k) :: ls) =
    (if Arith.equal_nata k (Arith.suc i)
      then SOME (Partial_Annotated_Clausal_Logic.Marked (ka, k) :: ls)
      else bt_cut i ls)
  | bt_cut i [] = NONE;

fun is_unit_clause_code A_ l m =
  (case List.filter
          (fn a =>
            not (Set.member A_ (Clausal_Logic.atm_of a)
                  (Set.image Clausal_Logic.atm_of
                    (Partial_Annotated_Clausal_Logic.lits_of m))))
          l
    of [] => NONE
    | [a] =>
      (if List.pred_list
            (fn c =>
              Set.member (Clausal_Logic.equal_literal A_)
                (Clausal_Logic.uminus_literal c)
                (Partial_Annotated_Clausal_Logic.lits_of m))
            (List.remove1 (Clausal_Logic.equal_literal A_) a l)
        then SOME a else NONE)
    | _ :: _ :: _ => NONE);

fun is_unit_clause A_ l m = is_unit_clause_code A_ l m;

fun find_first_unit_clause A_ (a :: l) m =
  (case is_unit_clause A_ a m of NONE => find_first_unit_clause A_ l m
    | SOME la => SOME (la, a))
  | find_first_unit_clause A_ [] uu = NONE;

fun do_propagate_step A_ s =
  (case s
    of (m, (n, (u, (k, Propo_CDCL.C_True)))) =>
      (case find_first_unit_clause A_ (n @ u) m
        of NONE => (m, (n, (u, (k, Propo_CDCL.C_True))))
        | SOME (l, c) =>
          (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: m,
            (n, (u, (k, Propo_CDCL.C_True)))))
    | (m, (n, (u, (k, Propo_CDCL.C_Clause ah)))) =>
      (m, (n, (u, (k, Propo_CDCL.C_Clause ah)))));

fun find_conflict A_ m [] = NONE
  | find_conflict A_ m (n :: ns) =
    (if List.pred_list
          (fn c =>
            Set.member (Clausal_Logic.equal_literal A_)
              (Clausal_Logic.uminus_literal c)
              (Partial_Annotated_Clausal_Logic.lits_of m))
          n
      then SOME n else find_conflict A_ m ns);

fun do_conflict_step A_ s =
  (case s
    of (m, (n, (u, (k, Propo_CDCL.C_True)))) =>
      (case find_conflict A_ m (n @ u)
        of NONE => (m, (n, (u, (k, Propo_CDCL.C_True))))
        | SOME a => (m, (n, (u, (k, Propo_CDCL.C_Clause a)))))
    | (m, (n, (u, (k, Propo_CDCL.C_Clause ah)))) =>
      (m, (n, (u, (k, Propo_CDCL.C_Clause ah)))));

fun do_cp_step A_ s = (do_propagate_step A_ o do_conflict_step A_) s;

fun rough_state_of_I (ConI x) = x;

fun id_of_I_to s = Con (rough_state_of_I s);

fun rough_state_of (Con x) = x;

fun do_cp_stepa s = Con (do_cp_step Arith.equal_nat (rough_state_of s));

fun do_skip_step
  (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls,
    (n, (u, (k, Propo_CDCL.C_Clause d))))
  = (if not (List.member (Clausal_Logic.equal_literal Arith.equal_nat) d
              (Clausal_Logic.uminus_literal l)) andalso
          not (List.null d)
      then (ls, (n, (u, (k, Propo_CDCL.C_Clause d))))
      else (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls,
             (n, (u, (k, Propo_CDCL.C_Clause d)))))
  | do_skip_step ([], va) = ([], va)
  | do_skip_step (Partial_Annotated_Clausal_Logic.Marked (vd, ve) :: vc, va) =
    (Partial_Annotated_Clausal_Logic.Marked (vd, ve) :: vc, va)
  | do_skip_step (v, (vb, (vd, (vf, Propo_CDCL.C_True)))) =
    (v, (vb, (vd, (vf, Propo_CDCL.C_True))));

fun equal_cdcl_state_I sa s =
  Product_Type.equal_proda
    (List.equal_list
      (Partial_Annotated_Clausal_Logic.equal_marked_lit Arith.equal_nat
        Arith.equal_nat
        (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat))))
    (Product_Type.equal_prod
      (List.equal_list
        (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat)))
      (Product_Type.equal_prod
        (List.equal_list
          (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat)))
        (Product_Type.equal_prod Arith.equal_nat
          (Propo_CDCL.equal_conflicting_clause
            (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat))))))
    (rough_state_of_I sa) (rough_state_of_I s);

fun equal_cdcl_state sa s =
  Product_Type.equal_proda
    (List.equal_list
      (Partial_Annotated_Clausal_Logic.equal_marked_lit Arith.equal_nat
        Arith.equal_nat
        (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat))))
    (Product_Type.equal_prod
      (List.equal_list
        (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat)))
      (Product_Type.equal_prod
        (List.equal_list
          (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat)))
        (Product_Type.equal_prod Arith.equal_nat
          (Propo_CDCL.equal_conflicting_clause
            (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat))))))
    (rough_state_of sa) (rough_state_of s);

fun do_full_cp_step s =
  let
    val sa = do_cp_stepa s;
  in
    (if equal_cdcl_state s sa then s else do_full_cp_step sa)
  end;

fun maximum_level_code A_ d m =
  Propo_CDCL.get_maximum_level A_ (Multiset.Mset d) m;

fun find_level_decomp A_ m [] d k = NONE
  | find_level_decomp A_ m (l :: ls) d k =
    let
      val (i, j) =
        (Propo_CDCL.get_rev_level A_ l Arith.zero_nat (List.rev m),
          maximum_level_code A_ (d @ ls) m);
    in
      (if Arith.equal_nata i k andalso Arith.less_nat j i then SOME (l, j)
        else find_level_decomp A_ m ls (l :: d) k)
    end;

fun do_backtrack_step A_ (m, (n, (u, (k, Propo_CDCL.C_Clause d)))) =
  (case find_level_decomp A_ m d [] k
    of NONE => (m, (n, (u, (k, Propo_CDCL.C_Clause d))))
    | SOME (l, j) =>
      (case bt_cut j m of NONE => (m, (n, (u, (k, Propo_CDCL.C_Clause d))))
        | SOME [] => (m, (n, (u, (k, Propo_CDCL.C_Clause d))))
        | SOME (Partial_Annotated_Clausal_Logic.Marked (_, _) :: ls) =>
          (Partial_Annotated_Clausal_Logic.Propagated (l, d) :: ls,
            (n, (d :: u, (j, Propo_CDCL.C_True))))
        | SOME (Partial_Annotated_Clausal_Logic.Propagated (_, _) :: _) =>
          (m, (n, (u, (k, Propo_CDCL.C_Clause d))))))
  | do_backtrack_step A_ (v, (vb, (vd, (vf, Propo_CDCL.C_True)))) =
    (v, (vb, (vd, (vf, Propo_CDCL.C_True))));

fun do_resolve_step
  (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls,
    (n, (u, (k, Propo_CDCL.C_Clause d))))
  = (if List.member (Clausal_Logic.equal_literal Arith.equal_nat) d
          (Clausal_Logic.uminus_literal l) andalso
          (Arith.equal_nata
             (maximum_level_code Arith.equal_nat
               (List.remove1 (Clausal_Logic.equal_literal Arith.equal_nat)
                 (Clausal_Logic.uminus_literal l) d)
               (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls))
             k orelse
            Arith.equal_nata k Arith.zero_nat)
      then (ls, (n, (u, (k, Propo_CDCL.C_Clause
                              (List.remdups
                                (Clausal_Logic.equal_literal Arith.equal_nat)
                                (List.remove1
                                   (Clausal_Logic.equal_literal Arith.equal_nat)
                                   l c @
                                  List.remove1
                                    (Clausal_Logic.equal_literal
                                      Arith.equal_nat)
                                    (Clausal_Logic.uminus_literal l) d))))))
      else (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls,
             (n, (u, (k, Propo_CDCL.C_Clause d)))))
  | do_resolve_step ([], va) = ([], va)
  | do_resolve_step (Partial_Annotated_Clausal_Logic.Marked (vd, ve) :: vc, va)
    = (Partial_Annotated_Clausal_Logic.Marked (vd, ve) :: vc, va)
  | do_resolve_step (v, (vb, (vd, (vf, Propo_CDCL.C_True)))) =
    (v, (vb, (vd, (vf, Propo_CDCL.C_True))));

fun find_first_unused_var A_ (a :: l) m =
  (case List.find
          (fn lit =>
            not (Set.member (Clausal_Logic.equal_literal A_) lit m) andalso
              not (Set.member (Clausal_Logic.equal_literal A_)
                    (Clausal_Logic.uminus_literal lit) m))
          a
    of NONE => find_first_unused_var A_ l m | SOME aa => SOME aa)
  | find_first_unused_var A_ [] uu = NONE;

fun do_decide_step A_ (m, (n, (u, (k, Propo_CDCL.C_True)))) =
  (case find_first_unused_var A_ n (Partial_Annotated_Clausal_Logic.lits_of m)
    of NONE => (m, (n, (u, (k, Propo_CDCL.C_True))))
    | SOME l =>
      (Partial_Annotated_Clausal_Logic.Marked (l, Arith.suc k) :: m,
        (n, (u, (Arith.plus_nat k Arith.one_nat, Propo_CDCL.C_True)))))
  | do_decide_step A_ (v, (vb, (vd, (vf, Propo_CDCL.C_Clause vh)))) =
    (v, (vb, (vd, (vf, Propo_CDCL.C_Clause vh))));

fun do_other_step s =
  let
    val t = do_skip_step s;
  in
    (if not (Product_Type.equal_proda
              (List.equal_list
                (Partial_Annotated_Clausal_Logic.equal_marked_lit
                  Arith.equal_nat Arith.equal_nat
                  (List.equal_list
                    (Clausal_Logic.equal_literal Arith.equal_nat))))
              (Product_Type.equal_prod
                (List.equal_list
                  (List.equal_list
                    (Clausal_Logic.equal_literal Arith.equal_nat)))
                (Product_Type.equal_prod
                  (List.equal_list
                    (List.equal_list
                      (Clausal_Logic.equal_literal Arith.equal_nat)))
                  (Product_Type.equal_prod Arith.equal_nat
                    (Propo_CDCL.equal_conflicting_clause
                      (List.equal_list
                        (Clausal_Logic.equal_literal Arith.equal_nat))))))
              t s)
      then t
      else let
             val u = do_resolve_step t;
           in
             (if not (Product_Type.equal_proda
                       (List.equal_list
                         (Partial_Annotated_Clausal_Logic.equal_marked_lit
                           Arith.equal_nat Arith.equal_nat
                           (List.equal_list
                             (Clausal_Logic.equal_literal Arith.equal_nat))))
                       (Product_Type.equal_prod
                         (List.equal_list
                           (List.equal_list
                             (Clausal_Logic.equal_literal Arith.equal_nat)))
                         (Product_Type.equal_prod
                           (List.equal_list
                             (List.equal_list
                               (Clausal_Logic.equal_literal Arith.equal_nat)))
                           (Product_Type.equal_prod Arith.equal_nat
                             (Propo_CDCL.equal_conflicting_clause
                               (List.equal_list
                                 (Clausal_Logic.equal_literal
                                   Arith.equal_nat))))))
                       u t)
               then u
               else let
                      val v = do_backtrack_step Arith.equal_nat u;
                    in
                      (if not (Product_Type.equal_proda
                                (List.equal_list
                                  (Partial_Annotated_Clausal_Logic.equal_marked_lit
                                    Arith.equal_nat Arith.equal_nat
                                    (List.equal_list
                                      (Clausal_Logic.equal_literal
Arith.equal_nat))))
                                (Product_Type.equal_prod
                                  (List.equal_list
                                    (List.equal_list
                                      (Clausal_Logic.equal_literal
Arith.equal_nat)))
                                  (Product_Type.equal_prod
                                    (List.equal_list
                                      (List.equal_list
(Clausal_Logic.equal_literal Arith.equal_nat)))
                                    (Product_Type.equal_prod Arith.equal_nat
                                      (Propo_CDCL.equal_conflicting_clause
(List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat))))))
                                v u)
                        then v else do_decide_step Arith.equal_nat v)
                    end)
           end)
  end;

fun do_other_stepa s = Con (do_other_step (rough_state_of s));

fun do_cdcl_s_step s =
  let
    val t = do_full_cp_step s;
  in
    (if not (equal_cdcl_state t s) then t
      else let
             val a = do_other_stepa t;
           in
             do_full_cp_step a
           end)
  end;

fun do_cdcl_s_stepa s = ConI (rough_state_of (do_cdcl_s_step (id_of_I_to s)));
fun do_all_cdcl_s s =
  let
    val t = do_cdcl_s_stepa s;
    val _ = writeln "step"
  in
    (if equal_cdcl_state_I t s then s else do_all_cdcl_s t)
  end;

end; (*struct CDCL_Implementation*)

\<close>
declare[[ML_print_depth=100]]
ML \<open>
open Clausal_Logic;
open CDCL_Implementation;
open Arith;
let
  val N = gene (Nat 2)
  val f = do_all_cdcl_s (ConI ([], (N, ([], (Nat 0, Propo_CDCL.C_True)))))
  in

  f
end
\<close>

(*>*)
end
