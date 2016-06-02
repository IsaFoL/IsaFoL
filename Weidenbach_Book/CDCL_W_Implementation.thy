theory CDCL_W_Implementation
imports DPLL_CDCL_W_Implementation CDCL_W_Termination
begin

subsection \<open>List-based CDCL Implementation\<close>

text \<open>We here have a very simple implementation of Weidenbach's CDCL, based on the same principle as
  the implementation of DPLL: iterating over-and-over on lists. We do not use any fancy
  data-structure (see the two-watched literals for a better suited data-structure).

  The goal was (as for DPLL) to test the infrastructure and see if an important lemma was missing to
  prove the correctness and the termination of a simple implementation.\<close>

subsubsection \<open>Types and Instantiation\<close>
notation image_mset (infixr "`#" 90)

type_synonym 'a cdcl\<^sub>W_restart_mark = "'a clause"

type_synonym 'v cdcl\<^sub>W_restart_ann_lit = "('v, 'v cdcl\<^sub>W_restart_mark) ann_lit"
type_synonym 'v cdcl\<^sub>W_restart_ann_lits = "('v, 'v cdcl\<^sub>W_restart_mark) ann_lits"
type_synonym 'v cdcl\<^sub>W_restart_state =
  "'v cdcl\<^sub>W_restart_ann_lits \<times> 'v clauses \<times> 'v clauses \<times> nat \<times> 'v clause option"

abbreviation raw_trail :: "'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'a" where
"raw_trail \<equiv> (\<lambda>(M, _). M)"

abbreviation raw_cons_trail :: "'a \<Rightarrow> 'a list \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'a list \<times> 'b \<times> 'c \<times> 'd \<times> 'e"
  where
"raw_cons_trail \<equiv> (\<lambda>L (M, S). (L#M, S))"

abbreviation raw_tl_trail :: "'a list \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'a list \<times> 'b \<times> 'c \<times> 'd \<times> 'e" where
"raw_tl_trail \<equiv> (\<lambda>(M, S). (tl M, S))"

abbreviation raw_init_clss :: "'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'b" where
"raw_init_clss \<equiv> \<lambda>(M, N, _). N"

abbreviation raw_learned_clss :: "'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'c" where
"raw_learned_clss \<equiv> \<lambda>(M, N, U, _). U"

abbreviation raw_backtrack_lvl :: "'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'd" where
"raw_backtrack_lvl \<equiv> \<lambda>(M, N, U, k, _). k"

abbreviation raw_update_backtrack_lvl :: "'d \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e"
  where
"raw_update_backtrack_lvl \<equiv> \<lambda>k (M, N, U, _, S).  (M, N, U, k, S)"

abbreviation raw_conflicting :: "'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'e" where
"raw_conflicting \<equiv> \<lambda>(M, N, U, k, D). D"

abbreviation raw_update_conflicting :: "'e \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e"
  where
"raw_update_conflicting \<equiv> \<lambda>S (M, N, U, k, _).  (M, N, U, k, S)"

abbreviation "S0_cdcl\<^sub>W_restart N \<equiv> (([], N, {#}, 0, None):: 'v cdcl\<^sub>W_restart_state)"

abbreviation raw_add_learned_clss where
"raw_add_learned_clss \<equiv> \<lambda>C (M, N, U, S). (M, N, {#C#} + U, S)"

abbreviation raw_remove_cls where
"raw_remove_cls \<equiv> \<lambda>C (M, N, U, S). (M, removeAll_mset C N, removeAll_mset C U, S)"

lemma raw_trail_conv: "raw_trail (M, N, U, k, D) = M" and
  clauses_conv: "raw_init_clss (M, N, U, k, D) = N" and
  raw_learned_clss_conv: "raw_learned_clss (M, N, U, k, D) = U" and
  raw_conflicting_conv: "raw_conflicting (M, N, U, k, D) = D" and
  raw_backtrack_lvl_conv: "raw_backtrack_lvl (M, N, U, k, D) = k"
  by auto

lemma state_conv:
  "S = (raw_trail S, raw_init_clss S, raw_learned_clss S, raw_backtrack_lvl S, raw_conflicting S)"
  by (cases S) auto


interpretation state\<^sub>W
  raw_trail raw_init_clss raw_learned_clss raw_backtrack_lvl raw_conflicting
  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, U, S). (M, N, {#C#} + U, S)"
  "\<lambda>C (M, N, U, S). (M, removeAll_mset C N, removeAll_mset C U, S)"
  "\<lambda>(k::nat) (M, N, U, _, D). (M, N, U, k, D)"
  "\<lambda>D (M, N, U, k, _). (M, N, U, k, D)"
  "\<lambda>N. ([], N, {#}, 0, None)"
  by unfold_locales auto

interpretation conflict_driven_clause_learning\<^sub>W raw_trail raw_init_clss raw_learned_clss raw_backtrack_lvl raw_conflicting
  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, U, S). (M, N, {#C#} + U, S)"
  "\<lambda>C (M, N, U, S). (M, removeAll_mset C N, removeAll_mset C U, S)"
  "\<lambda>(k::nat) (M, N, U, _, D). (M, N, U, k, D)"
  "\<lambda>D (M, N, U, k, _). (M, N, U, k, D)"
  "\<lambda>N. ([], N, {#}, 0, None)"
  by unfold_locales auto

declare clauses_def[simp]

lemma cdcl\<^sub>W_restart_state_eq_equality[iff]: "state_eq S T \<longleftrightarrow> S = T"
  unfolding state_eq_def by (cases S, cases T) auto
declare state_simp[simp del]

lemma reduce_trail_to_empty_trail[simp]:
  "reduce_trail_to F ([], aa, ab, ac, b) = ([], aa, ab, ac, b)"
  using reduce_trail_to.simps by auto

lemma raw_trail_reduce_trail_to_length_le:
  assumes "length F > length (raw_trail S)"
  shows "raw_trail (reduce_trail_to F S) = []"
  using assms trail_reduce_trail_to_length_le[of S F]
  by (cases S, cases "reduce_trail_to F S") auto

lemma reduce_trail_to:
  "reduce_trail_to F S =
    ((if length (raw_trail S) \<ge> length F
    then drop (length (raw_trail S) - length F) (raw_trail S)
    else []), raw_init_clss S, raw_learned_clss S, raw_backtrack_lvl S, raw_conflicting S)"
    (is "?S = _")
proof (induction F S rule: reduce_trail_to.induct)
  case (1 F S) note IH = this
  show ?case
    proof (cases "raw_trail S")
      case Nil
      then show ?thesis using IH by (cases S) auto
    next
      case (Cons L M)
      then show ?thesis
        apply (cases "Suc (length M) > length F")
         prefer 2 using IH reduce_trail_to_length_ne[of S F] apply (cases S) apply auto[]
        apply (subgoal_tac "Suc (length M) - length F = Suc (length M - length F)")
        using reduce_trail_to_length_ne[of S F] IH by (cases S) auto
    qed
qed

subsection \<open>CDCL Implementation\<close>
subsubsection \<open>Definition of the rules\<close>
paragraph \<open>Types\<close>
lemma true_raw_init_clss_remdups[simp]:
  "I \<Turnstile>s (mset \<circ> remdups) ` N \<longleftrightarrow>  I \<Turnstile>s mset ` N"
  by (simp add: true_clss_def)

lemma satisfiable_mset_remdups[simp]:
  "satisfiable ((mset \<circ> remdups) ` N) \<longleftrightarrow> satisfiable (mset ` N)"
unfolding satisfiable_carac[symmetric] by simp


type_synonym 'v cdcl\<^sub>W_restart_state_inv_st = "('v, 'v literal list) ann_lit list \<times>
  'v literal list list \<times> 'v literal list list \<times> nat \<times> 'v literal list option"

text \<open>We need some functions to convert between our abstract state @{typ "'v cdcl\<^sub>W_restart_state"} and the
 concrete state @{typ "'v cdcl\<^sub>W_restart_state_inv_st"}.\<close>

fun convert :: "('a, 'c list) ann_lit \<Rightarrow> ('a, 'c multiset) ann_lit"  where
"convert (Propagated L C) = Propagated L (mset C)" |
"convert (Decided K) = Decided K"

abbreviation convertC :: "'a list option \<Rightarrow> 'a multiset option"  where
"convertC \<equiv> map_option mset"

lemma convert_Propagated[elim!]:
  "convert z = Propagated L C \<Longrightarrow> (\<exists>C'. z = Propagated L C' \<and> C = mset C')"
  by (cases z) auto

lemma is_decided_convert[simp]: "is_decided (convert x) = is_decided x"
  by (cases x) auto

lemma get_level_map_convert[simp]:
  "get_level (map convert M) x = get_level M x"
  by (induction M rule: ann_lit_list_induct) (auto simp: comp_def)

lemma get_maximum_level_map_convert[simp]:
  "get_maximum_level (map convert M) D = get_maximum_level M D"
  by (induction D)
     (auto simp add: get_maximum_level_plus)

text \<open>Conversion function\<close>
fun toS :: "'v cdcl\<^sub>W_restart_state_inv_st \<Rightarrow> 'v cdcl\<^sub>W_restart_state" where
"toS (M, N, U, k, C) = (map convert M, mset (map mset N),  mset (map mset U), k, convertC C)"

text \<open>Definition an abstract type\<close>
typedef 'v cdcl\<^sub>W_restart_state_inv =  "{S::'v cdcl\<^sub>W_restart_state_inv_st. cdcl\<^sub>W_restart_all_struct_inv (toS S)}"
  morphisms rough_state_of state_of
proof
  show "([],[], [], 0, None) \<in> {S. cdcl\<^sub>W_restart_all_struct_inv (toS S)}"
    by (auto simp add: cdcl\<^sub>W_restart_all_struct_inv_def)
qed

instantiation cdcl\<^sub>W_restart_state_inv :: (type) equal
begin
definition equal_cdcl\<^sub>W_restart_state_inv :: "'v cdcl\<^sub>W_restart_state_inv \<Rightarrow> 'v cdcl\<^sub>W_restart_state_inv \<Rightarrow> bool" where
 "equal_cdcl\<^sub>W_restart_state_inv S S' = (rough_state_of S = rough_state_of S')"
instance
  by standard (simp add: rough_state_of_inject equal_cdcl\<^sub>W_restart_state_inv_def)
end

lemma lits_of_map_convert[simp]: "lits_of_l (map convert M) = lits_of_l M"
  by (induction M rule: ann_lit_list_induct) simp_all

lemma atm_lit_of_convert[simp]:
  "lit_of (convert x) =  lit_of x"
  by (cases x) auto

lemma undefined_lit_map_convert[iff]:
  "undefined_lit (map convert M) L \<longleftrightarrow> undefined_lit M L"
  by (auto simp add: defined_lit_map image_image)

lemma true_annot_map_convert[simp]: "map convert M \<Turnstile>a N \<longleftrightarrow> M \<Turnstile>a N"
  by (simp_all add: true_annot_def image_image lits_of_def)

lemma true_annots_map_convert[simp]: "map convert M \<Turnstile>as N \<longleftrightarrow> M \<Turnstile>as N"
  unfolding true_annots_def by auto

lemmas propagateE
lemma find_first_unit_clause_some_is_propagate:
  assumes H: "find_first_unit_clause (N @ U) M = Some (L, C)"
  shows "propagate (toS (M, N, U, k, None)) (toS (Propagated L C # M, N, U, k, None))"
  using assms
  by (auto dest!: find_first_unit_clause_some simp add: propagate.simps
    intro!: exI[of _ "mset C - {#L#}"])

subsubsection \<open>The Transitions\<close>
paragraph \<open>Propagate\<close>
definition do_propagate_step where
"do_propagate_step S =
  (case S of
    (M, N, U, k, None) \<Rightarrow>
      (case find_first_unit_clause (N @ U) M of
        Some (L, C) \<Rightarrow> (Propagated L C # M, N, U, k, None)
      | None \<Rightarrow> (M, N, U, k, None))
  | S \<Rightarrow> S)"

lemma do_propgate_step:
  "do_propagate_step S \<noteq> S \<Longrightarrow> propagate (toS S) (toS (do_propagate_step S))"
  apply (cases S, cases "raw_conflicting S")
  using find_first_unit_clause_some_is_propagate[of "raw_init_clss S" "raw_learned_clss S" "raw_trail S" _ _
    "raw_backtrack_lvl S"]
  by (auto simp add: do_propagate_step_def split: option.splits)

lemma do_propagate_step_option[simp]:
  "raw_conflicting S \<noteq> None \<Longrightarrow> do_propagate_step S = S"
  unfolding do_propagate_step_def by (cases S, cases "raw_conflicting S") auto

lemma do_propagate_step_no_step:
  assumes dist: "\<forall>c\<in>set (raw_init_clss S @ raw_learned_clss S). distinct c" and
  prop_step: "do_propagate_step S = S"
  shows "no_step propagate (toS S)"
proof (standard, standard)
  fix T
  assume "propagate (toS S) T"
  then obtain M N U k C L E where
    toSS: "toS S = (M, N, U, k, None)" and
    LE: "L \<in># E" and
    T: "T = (Propagated L E # M, N, U, k, None)" and
    MC: "M \<Turnstile>as CNot C" and
    undef: "undefined_lit M L" and
    CL: "C + {#L#} \<in># N + U"
    apply - by (cases "toS S") (auto elim!: propagateE)
  let ?M = "raw_trail S"
  let ?N = "raw_init_clss S"
  let ?U = "raw_learned_clss S"
  let ?k = "raw_backtrack_lvl S"
  let ?D = "None"
  have S: "S = (?M, ?N, ?U, ?k, ?D)"
    using toSS by (cases S, cases "raw_conflicting S") simp_all
  have S: "toS S = toS (?M, ?N, ?U, ?k, ?D)"
    unfolding S[symmetric] by simp

  have
    M: "M = map convert ?M" and
    N: "N = mset (map mset ?N)" and
    U: "U = mset (map mset ?U)"
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
  then show False using prop_step S unfolding do_propagate_step_def by (cases S) auto
qed

paragraph \<open>Conflict\<close>
fun find_conflict where
"find_conflict M [] = None" |
"find_conflict M (N # Ns) = (if (\<forall>c \<in> set N. -c \<in> lits_of_l M) then Some N else find_conflict M Ns)"

lemma find_conflict_Some:
  "find_conflict M Ns = Some N \<Longrightarrow> N \<in> set Ns \<and> M \<Turnstile>as CNot (mset N)"
  by (induction Ns rule: find_conflict.induct)
     (auto split: if_split_asm)

lemma find_conflict_None:
  "find_conflict M Ns = None \<longleftrightarrow> (\<forall>N \<in> set Ns. \<not>M \<Turnstile>as CNot (mset N))"
  by (induction Ns) auto

lemma find_conflict_None_no_confl:
  "find_conflict M (N@U) = None \<longleftrightarrow> no_step conflict (toS (M, N, U, k, None))"
  by (auto simp add: find_conflict_None conflict.simps)

definition do_conflict_step where
"do_conflict_step S =
  (case S of
    (M, N, U, k, None) \<Rightarrow>
      (case find_conflict M (N @ U) of
        Some a \<Rightarrow> (M, N, U, k, Some a)
      | None \<Rightarrow> (M, N, U, k, None))
  | S \<Rightarrow> S)"

lemma do_conflict_step:
  "do_conflict_step S \<noteq> S \<Longrightarrow> conflict (toS S) (toS (do_conflict_step S))"
  apply (cases S, cases "raw_conflicting S")
  unfolding conflict.simps do_conflict_step_def
  by (auto dest!:find_conflict_Some split: option.splits)

lemma do_conflict_step_no_step:
  "do_conflict_step S = S \<Longrightarrow> no_step conflict (toS S)"
  apply (cases S, cases "raw_conflicting S")
  unfolding do_conflict_step_def
  using find_conflict_None_no_confl[of "raw_trail S" "raw_init_clss S" "raw_learned_clss S"
      "raw_backtrack_lvl S"]
  by (auto split: option.splits elim!: conflictE)

lemma do_conflict_step_option[simp]:
  "raw_conflicting S \<noteq> None \<Longrightarrow> do_conflict_step S = S"
  unfolding do_conflict_step_def by (cases S, cases "raw_conflicting S") auto

lemma do_conflict_step_raw_conflicting[dest]:
  "do_conflict_step S \<noteq> S \<Longrightarrow> raw_conflicting (do_conflict_step S) \<noteq> None"
  unfolding do_conflict_step_def by (cases S, cases "raw_conflicting S") (auto split: option.splits)

definition do_cp_step where
"do_cp_step S =
  (do_propagate_step o do_conflict_step) S"

lemma cp_step_is_cdcl\<^sub>W_restart_cp:
  assumes H: "do_cp_step S \<noteq> S"
  shows "cdcl\<^sub>W_restart_cp (toS S) (toS (do_cp_step S))"
proof -
  show ?thesis
  proof (cases "do_conflict_step S \<noteq> S")
    case True
    then show ?thesis
      by (auto simp add: do_conflict_step do_conflict_step_raw_conflicting do_cp_step_def)
  next
    case False
    then have confl[simp]: "do_conflict_step S = S" by simp
    show ?thesis
      proof (cases "do_propagate_step S = S")
        case True
        then show ?thesis
        using H by (simp add: do_cp_step_def)
      next
        case False
        let ?S = "toS S"
        let ?T = "toS (do_propagate_step S)"
        let ?U = "toS (do_conflict_step (do_propagate_step S))"
        have propa: "propagate (toS S) ?T" using False do_propgate_step by blast
        moreover have ns: "no_step conflict (toS S)" using confl do_conflict_step_no_step by blast
        ultimately show ?thesis
          using cdcl\<^sub>W_restart_cp.intros(2)[of ?S ?T] confl unfolding do_cp_step_def by auto
      qed
  qed
qed

lemma do_cp_step_eq_no_prop_no_confl:
  "do_cp_step S = S \<Longrightarrow> do_conflict_step S = S \<and> do_propagate_step S = S"
  by (cases S, cases "raw_conflicting S")
    (auto simp add: do_conflict_step_def do_propagate_step_def do_cp_step_def split: option.splits)

lemma no_cdcl\<^sub>W_restart_cp_iff_no_propagate_no_conflict:
  "no_step cdcl\<^sub>W_restart_cp S \<longleftrightarrow> no_step propagate S \<and> no_step conflict S"
  by (auto simp: cdcl\<^sub>W_restart_cp.simps)

lemma do_cp_step_eq_no_step:
  assumes H: "do_cp_step S = S" and "\<forall>c \<in> set (raw_init_clss S @ raw_learned_clss S). distinct c"
  shows "no_step cdcl\<^sub>W_restart_cp (toS S)"
  unfolding no_cdcl\<^sub>W_restart_cp_iff_no_propagate_no_conflict
  using assms apply (cases S, cases "raw_conflicting S")
  using do_propagate_step_no_step[of S]
  by (auto dest!: do_cp_step_eq_no_prop_no_confl[simplified] do_conflict_step_no_step
    split: option.splits)

lemma cdcl\<^sub>W_restart_cp_cdcl\<^sub>W_restart_st: "cdcl\<^sub>W_restart_cp S S' \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S S'"
  by (simp add: cdcl\<^sub>W_restart_cp_tranclp_cdcl\<^sub>W_restart tranclp_into_rtranclp)

lemma cdcl\<^sub>W_restart_all_struct_inv_rough_state[simp]: "cdcl\<^sub>W_restart_all_struct_inv (toS (rough_state_of S))"
  using rough_state_of by auto

lemma [simp]: "cdcl\<^sub>W_restart_all_struct_inv (toS S) \<Longrightarrow> rough_state_of (state_of S) = S"
  by (simp add: state_of_inverse)

lemma rough_state_of_state_of_do_cp_step[simp]:
  "rough_state_of (state_of (do_cp_step (rough_state_of S))) = do_cp_step (rough_state_of S)"
proof -
  have "cdcl\<^sub>W_restart_all_struct_inv (toS (do_cp_step (rough_state_of S)))"
    apply (cases "do_cp_step (rough_state_of S) = (rough_state_of S)")
      apply simp
    using cp_step_is_cdcl\<^sub>W_restart_cp[of "rough_state_of S"] cdcl\<^sub>W_restart_all_struct_inv_rough_state[of S]
    cdcl\<^sub>W_restart_cp_cdcl\<^sub>W_restart_st rtranclp_cdcl\<^sub>W_restart_all_struct_inv_inv by blast
  then show ?thesis by auto
qed

paragraph \<open>Skip\<close>
fun do_skip_step :: "'v cdcl\<^sub>W_restart_state_inv_st \<Rightarrow> 'v cdcl\<^sub>W_restart_state_inv_st" where
"do_skip_step (Propagated L C # Ls,N,U,k, Some D) =
  (if -L \<notin> set D \<and> D \<noteq> []
  then (Ls, N, U, k, Some D)
  else (Propagated L C #Ls, N, U, k, Some D))" |
"do_skip_step S = S"

lemma do_skip_step:
  "do_skip_step S \<noteq> S \<Longrightarrow> skip (toS S) (toS (do_skip_step S))"
  apply (induction S rule: do_skip_step.induct)
  by (auto simp add: skip.simps)

lemma do_skip_step_no:
  "do_skip_step S = S \<Longrightarrow> no_step skip (toS S)"
  by (induction S rule: do_skip_step.induct)
     (auto simp add: other split: if_split_asm elim: skipE)

lemma do_skip_step_raw_trail_is_None[iff]:
  "do_skip_step S = (a, b, c, d, None) \<longleftrightarrow> S = (a, b, c, d, None)"
  by (cases S rule: do_skip_step.cases) auto

paragraph \<open>Resolve\<close>
fun maximum_level_code:: "'a literal list \<Rightarrow> ('a, 'a literal list) ann_lit list \<Rightarrow> nat"
  where
"maximum_level_code [] _ = 0" |
"maximum_level_code (L # Ls) M = max (get_level M L) (maximum_level_code Ls M)"

lemma maximum_level_code_eq_get_maximum_level[code, simp]:
  "maximum_level_code D M = get_maximum_level M (mset D)"
  by (induction D) (auto simp add: get_maximum_level_plus)

fun do_resolve_step :: "'v cdcl\<^sub>W_restart_state_inv_st \<Rightarrow> 'v cdcl\<^sub>W_restart_state_inv_st" where
"do_resolve_step (Propagated L C # Ls, N, U, k, Some D) =
  (if -L \<in> set D \<and> maximum_level_code (remove1 (-L) D) (Propagated L C # Ls) = k
  then (Ls, N, U, k, Some (remdups (remove1 L C @ remove1 (-L) D)))
  else (Propagated L C # Ls, N, U, k, Some D))" |
"do_resolve_step S = S"

lemma do_resolve_step:
  "cdcl\<^sub>W_restart_all_struct_inv (toS S) \<Longrightarrow> do_resolve_step S \<noteq> S
  \<Longrightarrow> resolve (toS S) (toS (do_resolve_step S))"
proof (induction S rule: do_resolve_step.induct)
  case (1 L C M N U k D)
  then have
    "- L \<in> set D" and
    M: "maximum_level_code (remove1 (-L) D) (Propagated L C # M) = k"
    by (cases "mset D - {#- L#} = {#}",
        auto dest!: get_maximum_level_exists_lit_of_max_level[of _ "Propagated L C # M"]
        split: if_split_asm)+
  have "every_mark_is_a_conflict (toS (Propagated L C # M, N, U, k, Some D))"
    using 1(1) unfolding cdcl\<^sub>W_restart_all_struct_inv_def cdcl\<^sub>W_restart_conflicting_def by fast
  then have "L \<in> set C" by fastforce
  then obtain C' where C: "mset C = C' + {#L#}"
    by (metis add.commute in_multiset_in_set insert_DiffM)
  obtain D' where D: "mset D = D' + {#-L#}"
    using \<open>- L \<in> set D\<close> by (metis add.commute in_multiset_in_set insert_DiffM)
  have D'L:  "D' + {#- L#} - {#-L#} = D'" by (auto simp add: multiset_eq_iff)

  have CL: "mset C - {#L#} + {#L#} = mset C" using \<open>L \<in> set C\<close> by (auto simp add: multiset_eq_iff)
  have "get_maximum_level (Propagated L (C' + {#L#}) # map convert M) D' = k"
    using M[simplified] unfolding maximum_level_code_eq_get_maximum_level C[symmetric] CL
    by (metis D D'L convert.simps(1) get_maximum_level_map_convert list.simps(9))
  then have
    "resolve
       (map convert (Propagated L C # M), mset `# mset N, mset `# mset U, k, Some (mset D))
       (map convert M, mset `# mset N, mset `# mset U, k,
         Some (((mset D - {#-L#}) #\<union> (mset C - {#L#}))))"
    unfolding resolve.simps
      by (simp add: C D)
  moreover have
    "(map convert (Propagated L C # M), mset `# mset N, mset `# mset U, k, Some (mset D))
     = toS (Propagated L C # M, N, U, k, Some D)"
    by (auto simp: mset_map)
  moreover
    have "distinct_mset (mset C)" and "distinct_mset (mset D)"
      using \<open>cdcl\<^sub>W_restart_all_struct_inv (toS (Propagated L C # M, N, U, k, Some D))\<close>
      unfolding cdcl\<^sub>W_restart_all_struct_inv_def distinct_cdcl\<^sub>W_restart_state_def
      by auto
    then have "(mset C - {#L#}) #\<union> (mset D - {#- L#}) =
      remdups_mset (mset C - {#L#} + (mset D - {#- L#}))"
      by (auto simp: distinct_mset_rempdups_union_mset)
    then have "(map convert M, mset `# mset N, mset `# mset U, k,
    Some ((mset D - {#- L#}) #\<union> (mset C - {#L#})))
    = toS (do_resolve_step (Propagated L C # M, N, U, k, Some D))"
    using \<open>- L \<in> set D\<close> M by (auto simp:ac_simps mset_map)
  ultimately show ?case
    by simp
qed auto

lemma do_resolve_step_no:
  "do_resolve_step S = S \<Longrightarrow> no_step resolve (toS S)"
  apply (cases S; cases "hd (raw_trail S)";cases "raw_trail S"; cases "raw_conflicting S")
  by (auto
    elim!: resolveE  split: if_split_asm
    dest!: union_single_eq_member
    simp del: in_multiset_in_set get_maximum_level_map_convert
    simp: get_maximum_level_map_convert[symmetric])

lemma  rough_state_of_state_of_resolve[simp]:
  "cdcl\<^sub>W_restart_all_struct_inv (toS S) \<Longrightarrow> rough_state_of (state_of (do_resolve_step S)) = do_resolve_step S"
  apply (rule state_of_inverse)
  apply (cases "do_resolve_step S = S")
   apply simp
  by (blast dest: other resolve bj do_resolve_step cdcl\<^sub>W_restart_all_struct_inv_inv)

lemma do_resolve_step_raw_trail_is_None[iff]:
  "do_resolve_step S = (a, b, c, d, None) \<longleftrightarrow> S = (a, b, c, d, None)"
  by (cases S rule: do_resolve_step.cases) auto

paragraph \<open>Backjumping\<close>
lemma get_all_ann_decomposition_map_convert:
  "(get_all_ann_decomposition (map convert M)) =
    map (\<lambda>(a, b). (map convert a, map convert b)) (get_all_ann_decomposition M)"
  apply (induction M rule: ann_lit_list_induct)
    apply simp
  by (rename_tac L xs, case_tac "get_all_ann_decomposition xs"; auto)+

lemma do_backtrack_step:
  assumes
    db: "do_backtrack_step S \<noteq> S" and
    inv: "cdcl\<^sub>W_restart_all_struct_inv (toS S)"
  shows "backtrack (toS S) (toS (do_backtrack_step S))"
  proof (cases S, cases "raw_conflicting S", goal_cases)
    case (1 M N U k E)
    then show ?case using db by auto
  next
    case (2 M N U k E C) note S = this(1) and confl = this(2)
    have E: "E = Some C" using S confl by auto

    obtain L j where fd: "find_level_decomp M C [] k = Some (L, j)"
      using db unfolding S E  by (cases C) (auto split: if_split_asm option.splits list.splits
        ann_lit.splits)
    have
      "L \<in> set C" and
      j: "get_maximum_level M (mset (remove1 L C)) = j" and
      levL: "get_level M L = k"
      using find_level_decomp_some[OF fd] by auto
    obtain C' where C: "mset C = mset C' + {#L#}"
      using \<open>L \<in> set C\<close> by (metis add.commute ex_mset in_multiset_in_set insert_DiffM)
    obtain M2 where M2: "bt_cut j M = Some M2"
      using db fd unfolding S E by (auto split: option.splits)
    have "no_dup M" and k: "k = count_decided (filter is_decided M)"
      using inv unfolding cdcl\<^sub>W_restart_all_struct_inv_def cdcl\<^sub>W_restart_M_level_inv_def S by (auto simp: comp_def)
    then obtain M1 K c where
      M1: "M2 = Decided K # M1" and lev_K: "get_level M K = j + 1" and
      c: "M = c @ M2 "
      using bt_cut_some_decomp[OF _ M2] by (cases M2) auto
     have "j \<le> k" unfolding c j[symmetric] k
      by (metis (mono_tags, lifting) count_decided_ge_get_maximum_level filter_cong filter_filter)
    have max_l_j: "maximum_level_code C' M = j"
      using db fd M2 C unfolding S E by (auto
          split: option.splits list.splits ann_lit.splits
          dest!: find_level_decomp_some)[1]
    have "get_maximum_level M (mset C) \<ge> k"
      using \<open>L \<in> set C\<close> levL get_maximum_level_ge_get_level by (metis set_mset_mset)
    moreover have "get_maximum_level M (mset C) \<le> k"
      using get_maximum_level_exists_lit_of_max_level[of "mset C" M] inv
        cdcl\<^sub>W_restart_M_level_inv_get_level_le_backtrack_lvl[of "toS S"]
      unfolding C cdcl\<^sub>W_restart_all_struct_inv_def S by (auto dest: sym[of "get_level _ _"])
    ultimately have "get_maximum_level M (mset C) = k" by auto

    obtain M2' where M2': "(M2, M2') \<in> set (get_all_ann_decomposition M)"
      using bt_cut_in_get_all_ann_decomposition[OF \<open>no_dup M\<close> M2] by metis
    have decomp:
      "(Decided K # (map convert M1),
      (map convert M2')) \<in>
      set (get_all_ann_decomposition (map convert M))"
      using imageI[of _ _ "\<lambda>(a, b). (map convert a, map convert b)", OF M2'] j
      unfolding S E M1 by (simp add: get_all_ann_decomposition_map_convert)
    show ?case
      apply (rule backtrack_rule)
        using M2 fd confl \<open>L \<in> set C\<close> j decomp levL \<open>get_maximum_level M (mset C) = k\<close>
        unfolding S E M1 apply (auto simp: mset_map)[6]
      using M2' M2 fd j lev_K unfolding S E M1 CDCL_W_Implementation.state_eq_def
      by (auto simp: comp_def ac_simps)[2]
qed

lemma map_eq_list_length:
  "map f L = L' \<Longrightarrow> length L = length L'"
  by auto

lemma map_mmset_of_mlit_eq_cons:
  assumes "map convert M = a @ c"
  obtains a' c' where
     "M = a' @ c'" and
     "a = map convert a'" and
     "c = map convert c'"
  using that[of "take (length a) M" "drop (length a) M"]
  assms by (metis append_eq_conv_conj append_take_drop_id drop_map take_map)

lemma Decided_convert_iff:
  "Decided K = convert za \<longleftrightarrow> za = Decided K"
  by (cases za) auto

lemma do_backtrack_step_no:
  assumes
    db: "do_backtrack_step S = S" and
    inv: "cdcl\<^sub>W_restart_all_struct_inv (toS S)"
  shows "no_step backtrack (toS S)"
proof (rule ccontr, cases S, cases "raw_conflicting S", goal_cases)
  case 1
  then show ?case using db by (auto split: option.splits elim: backtrackE)
next
  case (2 M N U k E C) note bt = this(1) and S = this(2) and confl = this(3)
  obtain K j M1 M2 L D where
    CE: "raw_conflicting S = Some D" and
    LD: "L \<in># mset D" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (raw_trail S))" and
    levL: "get_level (raw_trail S) L = raw_backtrack_lvl S"  and
    k: "get_level (raw_trail S) L = get_maximum_level (raw_trail S) (mset D)" and
    j: "get_maximum_level (raw_trail S) (remove1_mset L (mset D)) \<equiv> j" and
    lev_K: "get_level (raw_trail S) K = Suc j"
    using bt apply clarsimp
    apply (elim backtrackE)
    apply (cases S)
    by (auto simp add: get_all_ann_decomposition_map_convert reduce_trail_to
      Decided_convert_iff)
  obtain c where c: "raw_trail S = c @ M2 @ Decided K # M1"
    using decomp by blast
  have "k = count_decided (raw_trail S)" and n_d: "no_dup M"
    using inv S unfolding cdcl\<^sub>W_restart_all_struct_inv_def cdcl\<^sub>W_restart_M_level_inv_def
    by (auto simp: comp_def)
  then have "k > j"
    using j count_decided_ge_get_maximum_level[of "raw_trail S" "remove1_mset L (mset D)"]
    count_decided_ge_get_level[of K "raw_trail S"]
    unfolding k lev_K
    unfolding c by (auto simp: get_all_ann_decomposition_map_convert simp del: count_decided_ge_get_level)
  have [simp]: "L \<in> set D"
    using LD by auto
  have CD: "C =  D"
    using CE confl by auto
  obtain D' where
    E: "E = Some D" and
    DD': "mset D = {#L#} + mset D'"
    using that[of "remove1 L D"]
    using S CE confl LD by (auto simp add: insert_DiffM)
  have "find_level_decomp M D [] k \<noteq> None"
    apply rule
    apply (drule find_level_decomp_none[of _ _ _ _ L D'])
    using DD' \<open>k > j\<close> mset_eq_setD S levL unfolding k[symmetric] j[symmetric]
    by (auto simp: ac_simps)
  then obtain L' j' where fd_some: "find_level_decomp M D [] k = Some (L', j')"
    by (cases "find_level_decomp M D [] k") auto
  have L': "L' = L"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "L' \<in># mset (remove1 L D)"
        by (metis fd_some find_level_decomp_some in_set_remove1 set_mset_mset)
      then have "get_level M L' \<le> get_maximum_level M (mset (remove1 L D))"
        using get_maximum_level_ge_get_level by blast
      then show False using \<open>k > j\<close> j find_level_decomp_some[OF fd_some] S DD' by auto
    qed
  then have j': "j' = j" using find_level_decomp_some[OF fd_some] j S DD' by auto

  obtain c' M1' where cM: "M = c' @ Decided K # M1'"
    apply (rule map_mmset_of_mlit_eq_cons[of M "map convert (c @ M2)"
      "map convert (Decided K # M1)"])
      using c S apply simp
    apply (rule map_mmset_of_mlit_eq_cons[of _ "map convert [Decided K]" "map convert M1"])
     apply auto[]
    apply (rename_tac a b' aa b, case_tac aa)
     apply auto[]
    apply (rename_tac a b' aa b, case_tac aa)
    by auto
  have btc_none: "bt_cut j M \<noteq> None"
    apply (rule bt_cut_not_none[of M ])
      using n_d cM S lev_K S apply blast+
    using lev_K S by auto
  show ?case using db n_d unfolding S  E
    by (auto split: option.splits list.splits ann_lit.splits
      simp add: fd_some  L' j' btc_none
      dest: bt_cut_some_decomp)
qed

lemma rough_state_of_state_of_backtrack[simp]:
  assumes inv: "cdcl\<^sub>W_restart_all_struct_inv (toS S)"
  shows "rough_state_of (state_of (do_backtrack_step S))= do_backtrack_step S"
proof (rule state_of_inverse)
  consider
    (step) "backtrack (toS S) (toS (do_backtrack_step S))" |
     (0) "do_backtrack_step S = S"
    using do_backtrack_step inv by blast
  then show "do_backtrack_step S \<in> {S. cdcl\<^sub>W_restart_all_struct_inv (toS S)}"
    proof cases
      case 0
      thus ?thesis using inv by simp
    next
      case step
      then show ?thesis
        using inv
        by (auto dest!:  cdcl\<^sub>W_restart.other cdcl\<^sub>W_o.bj cdcl\<^sub>W_bj.backtrack intro: cdcl\<^sub>W_restart_all_struct_inv_inv)
    qed
qed

paragraph \<open>Decide\<close>
fun do_decide_step where
"do_decide_step (M, N, U, k, None) =
  (case find_first_unused_var N (lits_of_l M) of
    None \<Rightarrow> (M, N, U, k, None)
  | Some L \<Rightarrow> (Decided L # M, N, U, k+1, None))" |
"do_decide_step S = S"

lemma do_decide_step:
  "do_decide_step S \<noteq> S \<Longrightarrow> decide (toS S) (toS (do_decide_step S))"
  apply (cases S, cases "raw_conflicting S")
  defer
  apply (auto split: option.splits simp add: decide.simps
          dest: find_first_unused_var_undefined find_first_unused_var_Some
          intro: atms_of_atms_of_ms_mono)[1]
proof -
  fix a :: "('a, 'a literal list) ann_lit list" and
        b :: "'a literal list list" and  c :: "'a literal list list" and
        d :: nat and e :: "'a literal list option"
  {
    fix a :: "('a, 'a literal list) ann_lit list" and
        b :: "'a literal list list" and  c :: "'a literal list list" and
        d :: nat and x2 :: "'a literal" and m :: "'a literal list"
    assume a1: "m \<in> set b"
    assume "x2 \<in> set m"
    then have f2: "atm_of x2 \<in> atms_of (mset m)"
      by simp
    have "\<And>f. (f m::'a literal multiset) \<in> f ` set b"
      using a1 by blast
    then have "\<And>f. (atms_of (f m)::'a set) \<subseteq> atms_of_ms (f ` set b)"
     using atms_of_atms_of_ms_mono by blast
    then have "\<And>n f. (n::'a) \<in> atms_of_ms (f ` set b) \<or> n \<notin> atms_of (f m)"
      by (meson contra_subsetD)
    then have "atm_of x2 \<in> atms_of_ms (mset ` set b)"
      using f2 by blast
  } note H = this
  {
    fix m :: "'a literal list" and x2
    have "m \<in> set b \<Longrightarrow> x2 \<in> set m \<Longrightarrow> x2 \<notin> lits_of_l a \<Longrightarrow> - x2 \<notin> lits_of_l a \<Longrightarrow>
      \<exists>aa\<in>set b. \<not> atm_of ` set aa \<subseteq> atm_of ` lits_of_l a"
      by (meson atm_of_in_atm_of_set_in_uminus contra_subsetD rev_image_eqI)
  } note H' = this

  assume  "do_decide_step S \<noteq> S" and
     "S = (a, b, c, d, e)" and
     "raw_conflicting S = None"
  then show "decide (toS S) (toS (do_decide_step S))"
    using H H' by (auto split: option.splits simp: decide.simps defined_lit_map lits_of_def
      image_image atm_of_eq_atm_of dest!: find_first_unused_var_Some)
qed

lemma do_decide_step_no:
  "do_decide_step S = S \<Longrightarrow> no_step decide (toS S)"
  apply (cases S, cases "raw_conflicting S")
  apply (auto simp: atms_of_ms_mset_unfold  Decided_Propagated_in_iff_in_lits_of_l lits_of_def
      dest!: atm_of_in_atm_of_set_in_uminus
      elim!: decideE
      split: option.splits)+
  using atm_of_eq_atm_of by blast+


lemma rough_state_of_state_of_do_decide_step[simp]:
  "cdcl\<^sub>W_restart_all_struct_inv (toS S) \<Longrightarrow> rough_state_of (state_of (do_decide_step S)) = do_decide_step S"
proof (subst state_of_inverse, goal_cases)
  case 1
  then show ?case
    by (cases "do_decide_step S = S")
      (auto dest: do_decide_step decide other intro: cdcl\<^sub>W_restart_all_struct_inv_inv)
qed simp

lemma rough_state_of_state_of_do_skip_step[simp]:
  "cdcl\<^sub>W_restart_all_struct_inv (toS S) \<Longrightarrow> rough_state_of (state_of (do_skip_step S)) = do_skip_step S"
  apply (subst state_of_inverse, cases "do_skip_step S = S")
   apply simp
  by (blast dest: other skip bj do_skip_step cdcl\<^sub>W_restart_all_struct_inv_inv)+

subsubsection \<open>Code generation\<close>
paragraph \<open>Type definition\<close>
text \<open>There are two invariants: one while applying conflict and propagate and one for the other
 rules\<close>

declare rough_state_of_inverse[simp add]
definition Con where
  "Con xs = state_of (if cdcl\<^sub>W_restart_all_struct_inv (toS (fst xs, snd xs)) then xs
  else ([], [], [], 0, None))"

lemma [code abstype]:
 "Con (rough_state_of S) = S"
  using rough_state_of[of S] unfolding Con_def by simp

definition do_cp_step' where
"do_cp_step' S = state_of (do_cp_step (rough_state_of S))"

typedef 'v cdcl\<^sub>W_restart_state_inv_from_init_state =
  "{S:: 'v cdcl\<^sub>W_restart_state_inv_st. cdcl\<^sub>W_restart_all_struct_inv (toS S)
    \<and> cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (S0_cdcl\<^sub>W_restart (raw_init_clss (toS S))) (toS S)}"
  morphisms rough_state_from_init_state_of state_from_init_state_of
proof
  show "([],[], [], 0, None) \<in> {S. cdcl\<^sub>W_restart_all_struct_inv (toS S)
    \<and> cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (S0_cdcl\<^sub>W_restart (raw_init_clss (toS S))) (toS S)}"
    by (auto simp add: cdcl\<^sub>W_restart_all_struct_inv_def)
qed

instantiation cdcl\<^sub>W_restart_state_inv_from_init_state :: (type) equal
begin
definition equal_cdcl\<^sub>W_restart_state_inv_from_init_state :: "'v cdcl\<^sub>W_restart_state_inv_from_init_state \<Rightarrow>
  'v cdcl\<^sub>W_restart_state_inv_from_init_state \<Rightarrow> bool" where
 "equal_cdcl\<^sub>W_restart_state_inv_from_init_state S S' \<longleftrightarrow>
   (rough_state_from_init_state_of S = rough_state_from_init_state_of S')"
instance
  by standard (simp add: rough_state_from_init_state_of_inject
    equal_cdcl\<^sub>W_restart_state_inv_from_init_state_def)
end

definition ConI where
  "ConI S = state_from_init_state_of (if cdcl\<^sub>W_restart_all_struct_inv (toS (fst S, snd S))
    \<and> cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (S0_cdcl\<^sub>W_restart (raw_init_clss (toS S))) (toS S) then S else ([], [], [], 0, None))"

lemma [code abstype]:
  "ConI (rough_state_from_init_state_of S) = S"
  using rough_state_from_init_state_of[of S] unfolding ConI_def
  by (simp add: rough_state_from_init_state_of_inverse)

definition id_of_I_to:: "'v cdcl\<^sub>W_restart_state_inv_from_init_state \<Rightarrow> 'v cdcl\<^sub>W_restart_state_inv" where
"id_of_I_to S = state_of (rough_state_from_init_state_of S)"

lemma [code abstract]:
  "rough_state_of (id_of_I_to S) = rough_state_from_init_state_of S"
  unfolding id_of_I_to_def using rough_state_from_init_state_of[of S] by auto

paragraph \<open>Conflict and Propagate\<close>
function do_full1_cp_step :: "'v cdcl\<^sub>W_restart_state_inv \<Rightarrow> 'v cdcl\<^sub>W_restart_state_inv" where
"do_full1_cp_step S =
  (let S' = do_cp_step' S in
   if S = S' then S else do_full1_cp_step S')"
by auto
termination
proof (relation "{(T', T). (rough_state_of T', rough_state_of T) \<in> {(S', S).
  (toS S', toS S) \<in> {(S', S). cdcl\<^sub>W_restart_all_struct_inv S \<and> cdcl\<^sub>W_restart_cp S S'}}}", goal_cases)
  case 1
  show ?case
    using wf_if_measure_f[OF wf_if_measure_f[OF cdcl\<^sub>W_restart_cp_wf_all_inv, of "toS"], of rough_state_of] .
next
  case (2 S' S)
  then show ?case
    unfolding do_cp_step'_def
    apply simp
    by (metis cp_step_is_cdcl\<^sub>W_restart_cp rough_state_of_inverse)
qed

lemma do_full1_cp_step_fix_point_of_do_full1_cp_step:
  "do_cp_step(rough_state_of (do_full1_cp_step S)) = (rough_state_of (do_full1_cp_step S))"
  by (rule do_full1_cp_step.induct[of "\<lambda>S. do_cp_step(rough_state_of (do_full1_cp_step S))
       = (rough_state_of (do_full1_cp_step S))"])
    (metis (full_types) do_full1_cp_step.elims rough_state_of_state_of_do_cp_step do_cp_step'_def)

lemma in_clauses_rough_state_of_is_distinct:
  "c\<in>set (raw_init_clss (rough_state_of S) @ raw_learned_clss (rough_state_of S)) \<Longrightarrow> distinct c"
  apply (cases "rough_state_of S")
  using rough_state_of[of S] by (auto simp add: distinct_mset_set_distinct cdcl\<^sub>W_restart_all_struct_inv_def
    distinct_cdcl\<^sub>W_restart_state_def)

lemma do_full1_cp_step_full:
  "full cdcl\<^sub>W_restart_cp (toS (rough_state_of S))
    (toS (rough_state_of (do_full1_cp_step S)))"
  unfolding full_def
proof (rule conjI, induction S rule: do_full1_cp_step.induct)
  case (1 S)
  then have f1:
      "cdcl\<^sub>W_restart_cp\<^sup>*\<^sup>* (toS (do_cp_step (rough_state_of S))) (
        toS (rough_state_of (do_full1_cp_step (state_of (do_cp_step (rough_state_of S))))))
      \<or> state_of (do_cp_step (rough_state_of S)) = S"
    using rough_state_of_state_of_do_cp_step unfolding do_cp_step'_def by fastforce
  have f2: "\<And>c. (if c = state_of (do_cp_step (rough_state_of c))
       then c else do_full1_cp_step (state_of (do_cp_step (rough_state_of c))))
     = do_full1_cp_step c"
    by (metis (full_types) do_cp_step'_def do_full1_cp_step.simps)
  have f3: "\<not> cdcl\<^sub>W_restart_cp (toS (rough_state_of S)) (toS (do_cp_step (rough_state_of S)))
    \<or> state_of (do_cp_step (rough_state_of S)) = S
    \<or> cdcl\<^sub>W_restart_cp\<^sup>+\<^sup>+ (toS (rough_state_of S))
        (toS (rough_state_of (do_full1_cp_step (state_of (do_cp_step (rough_state_of S))))))"
    using f1 by (meson rtranclp_into_tranclp2)
  { assume "do_full1_cp_step S \<noteq> S"
    then have "do_cp_step (rough_state_of S) = rough_state_of S
        \<longrightarrow> cdcl\<^sub>W_restart_cp\<^sup>*\<^sup>* (toS (rough_state_of S)) (toS (rough_state_of (do_full1_cp_step S)))
      \<or> do_cp_step (rough_state_of S) \<noteq> rough_state_of S
        \<and> state_of (do_cp_step (rough_state_of S)) \<noteq> S"
      using f2 f1 by (metis (no_types))
    then have "do_cp_step (rough_state_of S) \<noteq> rough_state_of S
        \<and> state_of (do_cp_step (rough_state_of S)) \<noteq> S
      \<or> cdcl\<^sub>W_restart_cp\<^sup>*\<^sup>* (toS (rough_state_of S)) (toS (rough_state_of (do_full1_cp_step S)))"
      by (metis rough_state_of_state_of_do_cp_step)
    then have "cdcl\<^sub>W_restart_cp\<^sup>*\<^sup>* (toS (rough_state_of S)) (toS (rough_state_of (do_full1_cp_step S)))"
      using f3 f2 by (metis (no_types) cp_step_is_cdcl\<^sub>W_restart_cp tranclp_into_rtranclp) }
  then show ?case
    by fastforce
next
  show "no_step cdcl\<^sub>W_restart_cp (toS (rough_state_of (do_full1_cp_step S)))"
    apply (rule do_cp_step_eq_no_step[OF do_full1_cp_step_fix_point_of_do_full1_cp_step[of S]])
    using in_clauses_rough_state_of_is_distinct unfolding do_cp_step'_def by blast
qed

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
  assumes inv: "cdcl\<^sub>W_restart_all_struct_inv (toS S)" and
  st: "do_other_step S \<noteq> S"
  shows "cdcl\<^sub>W_o (toS S) (toS (do_other_step S))"
  using st inv by (auto split: if_split_asm
    simp add: Let_def
    dest!: do_skip_step do_resolve_step do_backtrack_step do_decide_step
    dest!: cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros)

lemma do_other_step_no:
  assumes inv: "cdcl\<^sub>W_restart_all_struct_inv (toS S)" and
  st: "do_other_step S = S"
  shows "no_step cdcl\<^sub>W_o (toS S)"
  using st inv by (auto split: if_split_asm elim: cdcl\<^sub>W_bjE
    simp add: Let_def cdcl\<^sub>W_bj.simps elim!: cdcl\<^sub>W_o.cases
    dest!: do_skip_step_no do_resolve_step_no do_backtrack_step_no do_decide_step_no)

lemma rough_state_of_state_of_do_other_step[simp]:
  "rough_state_of (state_of (do_other_step (rough_state_of S))) = do_other_step (rough_state_of S)"
proof (cases "do_other_step (rough_state_of S) = rough_state_of S")
  case True
  then show ?thesis by simp
next
  case False
  have "cdcl\<^sub>W_o (toS (rough_state_of S)) (toS (do_other_step (rough_state_of S)))"
    by (metis False cdcl\<^sub>W_restart_all_struct_inv_rough_state do_other_step["of" "rough_state_of S"])
  then have "cdcl\<^sub>W_restart_all_struct_inv (toS (do_other_step (rough_state_of S)))"
    using cdcl\<^sub>W_restart_all_struct_inv_inv cdcl\<^sub>W_restart_all_struct_inv_rough_state other by blast
  then show ?thesis
    by (simp add: CollectI state_of_inverse)
qed

definition do_other_step' where
"do_other_step' S =
  state_of (do_other_step (rough_state_of S))"

lemma rough_state_of_do_other_step'[code abstract]:
 "rough_state_of (do_other_step' S) = do_other_step (rough_state_of S)"
 apply (cases "do_other_step (rough_state_of S) = rough_state_of S")
   unfolding do_other_step'_def apply simp
 using do_other_step[of "rough_state_of S"] by (auto intro: cdcl\<^sub>W_restart_all_struct_inv_inv
   cdcl\<^sub>W_restart_all_struct_inv_rough_state other state_of_inverse)

definition do_cdcl\<^sub>W_restart_stgy_step where
"do_cdcl\<^sub>W_restart_stgy_step S =
   (let T = do_full1_cp_step S in
     if T \<noteq> S
     then T
     else
       (let U = (do_other_step' T) in
        (do_full1_cp_step U))) "

definition do_cdcl\<^sub>W_restart_stgy_step' where
"do_cdcl\<^sub>W_restart_stgy_step' S = state_from_init_state_of (rough_state_of (do_cdcl\<^sub>W_restart_stgy_step (id_of_I_to S)))"

lemma toS_do_full1_cp_step_not_eq: "do_full1_cp_step S \<noteq> S \<Longrightarrow>
    toS (rough_state_of S) \<noteq> toS (rough_state_of (do_full1_cp_step S))"
proof -
  assume a1: "do_full1_cp_step S \<noteq> S"
  then have "S \<noteq> do_cp_step' S"
    by fastforce
  then show ?thesis
    by (metis (no_types) cp_step_is_cdcl\<^sub>W_restart_cp do_cp_step'_def do_cp_step_eq_no_step
      do_full1_cp_step_fix_point_of_do_full1_cp_step in_clauses_rough_state_of_is_distinct
      rough_state_of_inverse)
qed

text \<open>@{term do_full1_cp_step} should not be unfolded anymore:\<close>
declare do_full1_cp_step.simps[simp del]

paragraph \<open>Correction of the transformation\<close>
lemma do_cdcl\<^sub>W_restart_stgy_step:
  assumes "do_cdcl\<^sub>W_restart_stgy_step S \<noteq> S"
  shows "cdcl\<^sub>W_restart_stgy (toS (rough_state_of S)) (toS (rough_state_of (do_cdcl\<^sub>W_restart_stgy_step S)))"
proof (cases "do_full1_cp_step S = S")
  case False
  then show ?thesis
    using assms do_full1_cp_step_full[of S] unfolding full_unfold do_cdcl\<^sub>W_restart_stgy_step_def
    by (auto intro!: cdcl\<^sub>W_restart_stgy.intros dest: toS_do_full1_cp_step_not_eq)
next
  case True
  have "cdcl\<^sub>W_o (toS (rough_state_of S)) (toS (rough_state_of (do_other_step' S)))"
    by (smt True assms cdcl\<^sub>W_restart_all_struct_inv_rough_state do_cdcl\<^sub>W_restart_stgy_step_def do_other_step
      rough_state_of_do_other_step' rough_state_of_inverse)
  moreover
    have
      np: "no_step propagate (toS (rough_state_of S))" and
      nc: "no_step conflict (toS (rough_state_of S))"
        apply (metis True do_cp_step_eq_no_prop_no_confl
          do_full1_cp_step_fix_point_of_do_full1_cp_step do_propagate_step_no_step
          in_clauses_rough_state_of_is_distinct)
      by (metis True do_conflict_step_no_step do_cp_step_eq_no_prop_no_confl
        do_full1_cp_step_fix_point_of_do_full1_cp_step)
    then have "no_step cdcl\<^sub>W_restart_cp (toS (rough_state_of S))"
      by (simp add: cdcl\<^sub>W_restart_cp.simps)
  moreover have "full cdcl\<^sub>W_restart_cp (toS (rough_state_of (do_other_step' S)))
    (toS (rough_state_of (do_full1_cp_step (do_other_step' S))))"
    using do_full1_cp_step_full by auto
  ultimately show ?thesis
    using assms True unfolding do_cdcl\<^sub>W_restart_stgy_step_def
    by (auto intro!: cdcl\<^sub>W_restart_stgy.other' dest: toS_do_full1_cp_step_not_eq)
qed

lemma length_raw_trail_toS[simp]:
  "length (raw_trail (toS S)) = length (raw_trail S)"
  by (cases S) auto

lemma raw_conflicting_noTrue_iff_toS[simp]:
  "raw_conflicting (toS S) \<noteq> None \<longleftrightarrow> raw_conflicting S \<noteq> None"
  by (cases S) auto

lemma raw_trail_toS_neq_imp_raw_trail_neq:
  "raw_trail (toS S) \<noteq> raw_trail (toS S') \<Longrightarrow> raw_trail S \<noteq> raw_trail S'"
  by (cases S, cases S') auto

lemma do_skip_step_raw_trail_changed_or_conflict:
  assumes d: "do_other_step S \<noteq> S"
  and inv: "cdcl\<^sub>W_restart_all_struct_inv (toS S)"
  shows "raw_trail S \<noteq> raw_trail (do_other_step S)"
proof -
  have M: "\<And>M K M1 c. M = c @ K # M1 \<Longrightarrow> Suc (length M1) \<le> length M"
    by auto
  have "cdcl\<^sub>W_restart_M_level_inv (toS S)"
    using inv unfolding cdcl\<^sub>W_restart_all_struct_inv_def by auto
  have "cdcl\<^sub>W_o (toS S) (toS (do_other_step S))" using do_other_step[OF inv d] .
  then show ?thesis
    using \<open>cdcl\<^sub>W_restart_M_level_inv (toS S)\<close>
    proof (induction "toS (do_other_step S)" rule: cdcl\<^sub>W_o_induct)
      case decide
      then show ?thesis
        by (auto simp add: raw_trail_toS_neq_imp_raw_trail_neq)[]
    next
    case (skip)
    then show ?case
      by (cases S; cases "do_other_step S") force
    next
      case (resolve)
      then show ?case
         by (cases S, cases "do_other_step S") force
    next
      case (backtrack L D K i M1 M2) note LD = this(2) and decomp = this(3) and confl_S = this(1)
        and i = this(6) and U = this(8)

      have
        bt: "raw_backtrack_lvl (toS S) = count_decided (raw_trail (toS S))" and
        "raw_trail (toS S) \<Turnstile>as CNot D" and
        cons: "consistent_interp (lits_of_l (raw_trail (toS S)))"
        using inv confl_S unfolding cdcl\<^sub>W_restart_all_struct_inv_def cdcl\<^sub>W_restart_M_level_inv_def
        cdcl\<^sub>W_restart_conflicting_def by simp_all
      then have "-L \<in> lits_of_l (raw_trail (toS S))"
        using LD true_annots_true_cls_def_iff_negation_in_model by blast
      then have "-L \<in> lits_of_l (raw_trail S)"
        by (cases S) (auto simp: lits_of_def)
      moreover have "consistent_interp (lits_of_l (raw_trail S))"
        using cons by (cases S) (auto simp: lits_of_def image_image)
      ultimately have "L \<notin> lits_of_l (raw_trail S)"
        using consistent_interp_def by blast

      moreover
        have "L \<in> lits_of_l (raw_trail (toS (do_other_step S)))"
          using U by auto
        then have "L \<in> lits_of_l (raw_trail (do_other_step S))"
          by (cases "do_other_step S") (auto simp: lits_of_def)
      ultimately show ?thesis
        by metis
    qed
qed

lemma do_full1_cp_step_induct:
  "(\<And>S. (S \<noteq>  do_cp_step' S \<Longrightarrow> P (do_cp_step' S)) \<Longrightarrow> P S) \<Longrightarrow> P a0"
  using do_full1_cp_step.induct by metis

lemma do_cp_step_neq_raw_trail_increase:
  "\<exists>c. raw_trail (do_cp_step S) = c @ raw_trail  S \<and>(\<forall>m \<in> set c. \<not> is_decided m)"
  by (cases S, cases "raw_conflicting S")
     (auto simp add: do_cp_step_def do_conflict_step_def do_propagate_step_def split: option.splits)

lemma do_full1_cp_step_neq_raw_trail_increase:
  "\<exists>c. raw_trail (rough_state_of (do_full1_cp_step S)) = c @ raw_trail (rough_state_of S)
    \<and> (\<forall>m \<in> set c. \<not> is_decided m)"
  apply (induction rule: do_full1_cp_step_induct)
  apply (rename_tac S, case_tac "do_cp_step' S = S")
    apply (simp add: do_full1_cp_step.simps)
  by (smt Un_iff append_assoc do_cp_step'_def do_cp_step_neq_raw_trail_increase do_full1_cp_step.simps
    rough_state_of_state_of_do_cp_step set_append)

lemma do_cp_step_raw_conflicting:
  "raw_conflicting (rough_state_of S) \<noteq> None \<Longrightarrow> do_cp_step' S = S"
  unfolding do_cp_step'_def do_cp_step_def by simp

lemma do_full1_cp_step_raw_conflicting:
  "raw_conflicting (rough_state_of S) \<noteq> None \<Longrightarrow> do_full1_cp_step S = S"
  unfolding do_cp_step'_def do_cp_step_def
  apply (induction rule: do_full1_cp_step_induct)
  by (rename_tac S, case_tac "S \<noteq> do_cp_step' S")
   (auto simp add: do_full1_cp_step.simps do_cp_step_raw_conflicting)

lemma do_decide_step_not_raw_conflicting_one_more_decide:
  assumes
    "raw_conflicting S = None" and
    "do_decide_step S \<noteq> S"
  shows "Suc (length (filter is_decided (raw_trail S)))
    = length (filter is_decided (raw_trail (do_decide_step S)))"
  using assms unfolding do_other_step'_def
  by (cases S) (auto simp: Let_def split: if_split_asm option.splits
     dest!: find_first_unused_var_Some_not_all_incl)

lemma do_decide_step_not_raw_conflicting_one_more_decide_bt:
  assumes "raw_conflicting S \<noteq> None" and
  "do_decide_step S \<noteq> S"
  shows "length (filter is_decided (raw_trail S)) < length (filter is_decided (raw_trail (do_decide_step S)))"
  using assms unfolding do_other_step'_def by (cases S, cases "raw_conflicting S")
    (auto simp add: Let_def split: if_split_asm option.splits)

lemma count_decided_raw_trail_toS:
  "count_decided (raw_trail (toS S)) =  count_decided (raw_trail S)"
  by (cases S) (auto simp: comp_def)

lemma do_other_step_not_raw_conflicting_one_more_decide_bt:
  assumes
    "raw_conflicting (rough_state_of S) \<noteq> None" and
    "raw_conflicting (rough_state_of (do_other_step' S)) = None" and
    "do_other_step' S \<noteq> S"
  shows "count_decided (raw_trail (rough_state_of S))
    > count_decided (raw_trail (rough_state_of (do_other_step' S)))"
proof (cases S, goal_cases)
  case (1 y) note S = this(1) and inv = this(2)
  obtain M N U k E where y: "y = (M, N, U, k, Some E)"
    using assms(1) S inv by (cases y, cases "raw_conflicting y") auto
  have M: "rough_state_of (state_of (M, N, U, k,  Some E)) = (M, N, U, k,  Some E)"
    using inv y by (auto simp add: state_of_inverse)
  have bt: "do_other_step' S = state_of (do_backtrack_step (rough_state_of S))"
    proof (cases "rough_state_of S" rule: do_decide_step.cases)
      case 1
      then show ?thesis
        using assms(1,2) by auto[]
    next
      case (2 v vb vd vf vh)
      have f3: "\<And>c. (if do_skip_step (rough_state_of c) \<noteq> rough_state_of c
        then do_skip_step (rough_state_of c)
        else if do_resolve_step (do_skip_step (rough_state_of c)) \<noteq> do_skip_step (rough_state_of c)
             then do_resolve_step (do_skip_step (rough_state_of c))
             else if do_backtrack_step (do_resolve_step (do_skip_step (rough_state_of c)))
               \<noteq> do_resolve_step (do_skip_step (rough_state_of c))
             then do_backtrack_step (do_resolve_step (do_skip_step (rough_state_of c)))
             else do_decide_step (do_backtrack_step (do_resolve_step
               (do_skip_step (rough_state_of c)))))
        = rough_state_of (do_other_step' c)"
        by (simp add: rough_state_of_do_other_step')
      have "(raw_trail (rough_state_of (do_other_step' S)), raw_init_clss (rough_state_of (do_other_step' S)),
          raw_learned_clss (rough_state_of (do_other_step' S)),
          raw_backtrack_lvl (rough_state_of (do_other_step' S)), None)
        = rough_state_of (do_other_step' S)"
        using assms(2) by (metis (no_types) state_conv)
      then show ?thesis
        using f3 2 by (metis (no_types) do_decide_step.simps(2) do_resolve_step_raw_trail_is_None
          do_skip_step_raw_trail_is_None rough_state_of_inverse)
    qed
  have
    bt: "raw_backtrack_lvl (toS y) = count_decided (raw_trail (toS y))"
    using inv unfolding cdcl\<^sub>W_restart_all_struct_inv_def cdcl\<^sub>W_restart_M_level_inv_def
    cdcl\<^sub>W_restart_conflicting_def by simp_all
  have confl_y:  "raw_conflicting (toS (rough_state_of (do_other_step' (state_of y)))) = None"
   using assms(2) y S raw_conflicting_noTrue_iff_toS by blast
  have "backtrack (toS (rough_state_of S))
     (toS (rough_state_of (do_other_step' (state_of y)))) \<or>
    resolve (toS (rough_state_of S))
     (toS (rough_state_of (do_other_step' (state_of y)))) \<or>
    skip (toS (rough_state_of S))
     (toS (rough_state_of (do_other_step' (state_of y))))"
    proof -
      have f1: "(M, N, U, k, Some E) = rough_state_of S"
        by (simp add: M S y)
      then have f2: "do_other_step (M, N, U, k, Some E) \<noteq> (M, N, U, k, Some E)"
        by (metis assms(3) rough_state_of_do_other_step' rough_state_of_inject)
      have "cdcl\<^sub>W_restart_all_struct_inv (toS (M, N, U, k, Some E))"
        using f1 by simp
      then have "cdcl\<^sub>W_o (toS (M, N, U, k, Some E)) (toS (do_other_step (M, N, U, k, Some E)))"
        using f2 do_other_step by blast
      then have f3: "cdcl\<^sub>W_o (toS (rough_state_of S))
         (toS (rough_state_of (do_other_step' (state_of (M, N, U, k, Some E)))))"
        using f1 by (simp add: rough_state_of_do_other_step')
      have "\<not> decide (toS (rough_state_of S))
        (toS (rough_state_of (do_other_step' (state_of (M, N, U, k, Some E)))))"
        using f1 by (metis (no_types) do_decide_step.simps(2) do_decide_step_no)
      then show ?thesis
        using f3 cdcl\<^sub>W_o_rule_cases y by blast
    qed
  then have bt: "backtrack (toS (rough_state_of S))
     (toS (rough_state_of (do_other_step' (state_of y))))"
    using confl_y by (cases "rough_state_of S") (auto elim!: resolveE skipE)
moreover
  have "no_dup (raw_trail (rough_state_of S))"
    using rough_state_of[of S] unfolding cdcl\<^sub>W_restart_all_struct_inv_def cdcl\<^sub>W_restart_M_level_inv_def
    by (cases S) (auto simp: comp_def)
have "cdcl\<^sub>W_restart_M_level_inv (toS (rough_state_of S)) " and
  "cdcl\<^sub>W_restart_M_level_inv  (toS (rough_state_of (do_other_step' (state_of y))))"
    using inv apply (simp add: cdcl\<^sub>W_restart_all_struct_inv_def S)
  using cdcl\<^sub>W_restart_all_struct_inv_def cdcl\<^sub>W_restart_all_struct_inv_rough_state by blast
then show ?case
    using backtrack_lvl_backtrack_decrease[OF _ bt]
    using S unfolding  cdcl\<^sub>W_restart_M_level_inv_def
    by (simp add: comp_def count_decided_raw_trail_toS)
qed

lemma do_other_step_not_raw_conflicting_one_more_decide:
  assumes "raw_conflicting (rough_state_of S) = None" and
  "do_other_step' S \<noteq> S"
  shows "1 + length (filter is_decided (raw_trail (rough_state_of S)))
    = length (filter is_decided (raw_trail (rough_state_of (do_other_step' S))))"
proof (cases S, goal_cases)
  case (1 y) note S = this(1) and inv = this(2)
  obtain M N U k where y: "y = (M, N, U, k, None)" using assms(1) S inv by (cases y) auto
  have M: "rough_state_of (state_of (M, N, U, k, None)) = (M, N, U, k, None)"
    using inv y by (auto simp add: state_of_inverse)
  have "state_of (do_decide_step (M, N, U, k, None)) \<noteq> state_of (M, N, U, k, None)"
    using assms(2) unfolding do_other_step'_def y inv S by (auto simp add: M)
  then have f4: "do_skip_step (rough_state_of S) = rough_state_of S"
    unfolding S M y by (metis (full_types) do_skip_step.simps(4))
  have f5: "do_resolve_step (rough_state_of S) = rough_state_of S"
    unfolding S M y by (metis (no_types) do_resolve_step.simps(4))
  have f6: "do_backtrack_step (rough_state_of S) = rough_state_of S"
    unfolding S M y by (metis (no_types) do_backtrack_step.simps(2))
  have "do_other_step (rough_state_of S) \<noteq> rough_state_of S"
    using assms(2) unfolding S M y do_other_step'_def by (metis (no_types))
  then show ?case
    using f6 f5 f4 by (simp add: assms(1) do_decide_step_not_raw_conflicting_one_more_decide
      do_other_step'_def)
qed

lemma rough_state_of_state_of_do_skip_step_rough_state_of[simp]:
  "rough_state_of (state_of (do_skip_step (rough_state_of S))) = do_skip_step (rough_state_of S)"
  by (smt do_other_step.simps rough_state_of_inverse rough_state_of_state_of_do_other_step)

lemma raw_conflicting_do_resolve_step_iff[iff]:
  "raw_conflicting (do_resolve_step S) = None \<longleftrightarrow> raw_conflicting S = None"
  by (cases S rule: do_resolve_step.cases)
   (auto simp add: Let_def split: option.splits)

lemma raw_conflicting_do_skip_step_iff[iff]:
  "raw_conflicting (do_skip_step S) = None \<longleftrightarrow> raw_conflicting S = None"
  by (cases S rule: do_skip_step.cases)
     (auto simp add: Let_def split: option.splits)

lemma raw_conflicting_do_decide_step_iff[iff]:
  "raw_conflicting (do_decide_step S) = None \<longleftrightarrow> raw_conflicting S = None"
  by (cases S rule: do_decide_step.cases)
     (auto simp add: Let_def split: option.splits)

lemma raw_conflicting_do_backtrack_step_imp[simp]:
  "do_backtrack_step S \<noteq> S \<Longrightarrow> raw_conflicting (do_backtrack_step S) = None"
  by (cases S rule: do_backtrack_step.cases)
     (auto simp add: Let_def split: list.splits option.splits ann_lit.splits)

lemma do_skip_step_eq_iff_raw_trail_eq:
  "do_skip_step S = S \<longleftrightarrow> raw_trail (do_skip_step S) = raw_trail S"
  by (cases S rule: do_skip_step.cases) auto

lemma do_decide_step_eq_iff_raw_trail_eq:
  "do_decide_step S = S \<longleftrightarrow> raw_trail (do_decide_step S) = raw_trail S"
  by (cases S rule: do_decide_step.cases) (auto split: option.split)

lemma do_backtrack_step_eq_iff_raw_trail_eq:
  assumes "no_dup (raw_trail S)"
  shows "do_backtrack_step S = S \<longleftrightarrow> raw_trail (do_backtrack_step S) = raw_trail S"
  using assms apply (cases S rule: do_backtrack_step.cases)
  by (auto split: option.split list.splits ann_lit.splits
     simp: comp_def
     dest!: bt_cut_in_get_all_ann_decomposition)

lemma do_resolve_step_eq_iff_raw_trail_eq:
  "do_resolve_step S = S \<longleftrightarrow> raw_trail (do_resolve_step S) = raw_trail S"
  by (cases S rule: do_resolve_step.cases) auto

lemma do_other_step_eq_iff_raw_trail_eq:
  assumes "no_dup (raw_trail S)"
  shows "raw_trail (do_other_step S) = raw_trail S \<longleftrightarrow> do_other_step S = S"
  using assms
  by (auto simp add: Let_def do_skip_step_eq_iff_raw_trail_eq[symmetric]
    do_decide_step_eq_iff_raw_trail_eq[symmetric] do_backtrack_step_eq_iff_raw_trail_eq[symmetric]
    do_resolve_step_eq_iff_raw_trail_eq[symmetric])


lemma do_full1_cp_step_do_other_step'_normal_form[dest!]:
  assumes H: "do_full1_cp_step (do_other_step' S) = S"
  shows "do_other_step' S = S \<and> do_full1_cp_step S = S"
proof -
  let ?T = "do_other_step' S"
  { assume confl: "raw_conflicting (rough_state_of ?T) \<noteq> None"
    then have tr: "raw_trail (rough_state_of (do_full1_cp_step ?T)) = raw_trail (rough_state_of ?T)"
      using do_full1_cp_step_raw_conflicting[of ?T] by auto
    have "raw_trail (rough_state_of (do_full1_cp_step (do_other_step' S))) = raw_trail (rough_state_of S)"
      using arg_cong[OF H, of "\<lambda>S. raw_trail (rough_state_of S)"] .
    then have "raw_trail (rough_state_of (do_other_step' S)) = raw_trail (rough_state_of S)"
       by (auto simp add: do_full1_cp_step_raw_conflicting confl)
    then have "do_other_step' S = S"
      using assms confl
      by (simp add: do_other_step_eq_iff_raw_trail_eq do_other_step'_def
        do_full1_cp_step_raw_conflicting
              del: do_other_step.simps)

  }
  moreover {
    assume eq[simp]: "do_other_step' S = S"
    obtain c where c: "raw_trail (rough_state_of (do_full1_cp_step S)) = c @ raw_trail (rough_state_of S)"
      using do_full1_cp_step_neq_raw_trail_increase by auto

    moreover have "raw_trail (rough_state_of (do_full1_cp_step S)) = raw_trail (rough_state_of S)"
      using arg_cong[OF H, of "\<lambda>S. raw_trail (rough_state_of S)"] by simp
    finally have "c = []" by blast
    then have "do_full1_cp_step S = S" using assms by auto
    }
  moreover {
    assume confl: "raw_conflicting (rough_state_of ?T) = None" and neq: "do_other_step' S \<noteq> S"
    obtain c where
      c: "raw_trail (rough_state_of (do_full1_cp_step ?T)) = c @ raw_trail (rough_state_of ?T)" and
      nm: "\<forall>m\<in>set c. \<not> is_decided m"
      using do_full1_cp_step_neq_raw_trail_increase by auto
    have "length (filter is_decided (raw_trail (rough_state_of (do_full1_cp_step ?T))))
       = length (filter is_decided (raw_trail (rough_state_of ?T)))" using nm unfolding c by force
    moreover have "length (filter is_decided (raw_trail (rough_state_of S)))
       \<noteq> length (filter is_decided  (raw_trail (rough_state_of ?T)))"
      using do_other_step_not_raw_conflicting_one_more_decide[OF _ neq]
      do_other_step_not_raw_conflicting_one_more_decide_bt[of S, OF _ confl neq]
      by linarith
    finally have False unfolding H by blast
  }
  ultimately show ?thesis by blast
qed

lemma do_cdcl\<^sub>W_restart_stgy_step_no:
  assumes S: "do_cdcl\<^sub>W_restart_stgy_step S = S"
  shows "no_step cdcl\<^sub>W_restart_stgy (toS (rough_state_of S))"
proof -
  {
    fix S'
    assume "full1 cdcl\<^sub>W_restart_cp (toS (rough_state_of S)) S'"
    then have False
      using do_full1_cp_step_full[of S] unfolding full_def S rtranclp_unfold full1_def
      by (smt assms do_cdcl\<^sub>W_restart_stgy_step_def tranclpD)
  }
  moreover {
    fix S' S''
    assume " cdcl\<^sub>W_o (toS (rough_state_of S)) S'" and
     "no_step propagate (toS (rough_state_of S))" and
     "no_step conflict (toS (rough_state_of S))" and
     "full cdcl\<^sub>W_restart_cp S' S''"
    then have False
      using assms unfolding do_cdcl\<^sub>W_restart_stgy_step_def
      by (smt cdcl\<^sub>W_restart_all_struct_inv_rough_state do_full1_cp_step_do_other_step'_normal_form
        do_other_step_no rough_state_of_do_other_step')
  }
  ultimately show ?thesis using assms by (force simp: cdcl\<^sub>W_restart_cp.simps cdcl\<^sub>W_restart_stgy.simps)
qed

lemma toS_rough_state_of_state_of_rough_state_from_init_state_of[simp]:
  "toS (rough_state_of (state_of (rough_state_from_init_state_of S)))
    = toS (rough_state_from_init_state_of S)"
  using rough_state_from_init_state_of[of S] by (auto simp add: state_of_inverse)

lemma cdcl\<^sub>W_restart_cp_is_rtranclp_cdcl\<^sub>W_restart: "cdcl\<^sub>W_restart_cp S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
  apply (induction rule: cdcl\<^sub>W_restart_cp.induct)
   using conflict apply blast
  using propagate by blast

lemma rtranclp_cdcl\<^sub>W_restart_cp_is_rtranclp_cdcl\<^sub>W_restart: "cdcl\<^sub>W_restart_cp\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
  apply (induction rule: rtranclp_induct)
    apply simp
  by (fastforce dest!: cdcl\<^sub>W_restart_cp_is_rtranclp_cdcl\<^sub>W_restart)

lemma cdcl\<^sub>W_restart_stgy_is_rtranclp_cdcl\<^sub>W_restart:
  "cdcl\<^sub>W_restart_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
  apply (induction rule: cdcl\<^sub>W_restart_stgy.induct)
   using cdcl\<^sub>W_restart_stgy.conflict' rtranclp_cdcl\<^sub>W_restart_stgy_rtranclp_cdcl\<^sub>W_restart apply blast
  unfolding full_def by (fastforce dest!:other rtranclp_cdcl\<^sub>W_restart_cp_is_rtranclp_cdcl\<^sub>W_restart)

lemma cdcl\<^sub>W_restart_stgy_init_raw_init_clss:
  "cdcl\<^sub>W_restart_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_M_level_inv S \<Longrightarrow> raw_init_clss S = raw_init_clss T"
  using cdcl\<^sub>W_restart_stgy_no_more_init_clss by blast


lemma clauses_toS_rough_state_of_do_cdcl\<^sub>W_restart_stgy_step[simp]:
  "raw_init_clss (toS (rough_state_of (do_cdcl\<^sub>W_restart_stgy_step (state_of (rough_state_from_init_state_of S)))))
    = raw_init_clss (toS (rough_state_from_init_state_of S))" (is "_ = raw_init_clss (toS ?S)")
  apply (cases "do_cdcl\<^sub>W_restart_stgy_step (state_of ?S) = state_of ?S")
    apply simp
  by (metis cdcl\<^sub>W_restart_all_struct_inv_def cdcl\<^sub>W_restart_all_struct_inv_rough_state cdcl\<^sub>W_restart_stgy_no_more_init_clss
    do_cdcl\<^sub>W_restart_stgy_step toS_rough_state_of_state_of_rough_state_from_init_state_of)

lemma rough_state_from_init_state_of_do_cdcl\<^sub>W_restart_stgy_step'[code abstract]:
 "rough_state_from_init_state_of (do_cdcl\<^sub>W_restart_stgy_step' S) =
   rough_state_of (do_cdcl\<^sub>W_restart_stgy_step (id_of_I_to S))"
proof -
  let ?S = "(rough_state_from_init_state_of S)"
  have "cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (S0_cdcl\<^sub>W_restart (raw_init_clss (toS (rough_state_from_init_state_of S))))
    (toS (rough_state_from_init_state_of S))"
    using rough_state_from_init_state_of[of S] by auto
  moreover have "cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>*
                  (toS (rough_state_from_init_state_of S))
                  (toS (rough_state_of (do_cdcl\<^sub>W_restart_stgy_step
                    (state_of (rough_state_from_init_state_of S)))))"
     using do_cdcl\<^sub>W_restart_stgy_step[of "state_of ?S"]
     by (cases "do_cdcl\<^sub>W_restart_stgy_step (state_of ?S) = state_of ?S") auto
  ultimately show ?thesis
    unfolding do_cdcl\<^sub>W_restart_stgy_step'_def id_of_I_to_def
    by (auto intro!: state_from_init_state_of_inverse)
qed

paragraph \<open>All rules together\<close>
function do_all_cdcl\<^sub>W_restart_stgy where
"do_all_cdcl\<^sub>W_restart_stgy S =
  (let T = do_cdcl\<^sub>W_restart_stgy_step' S in
  if T = S then S else do_all_cdcl\<^sub>W_restart_stgy T)"
by fast+
termination
proof (relation "{(T, S).
    (cdcl\<^sub>W_restart_measure (toS (rough_state_from_init_state_of T)),
    cdcl\<^sub>W_restart_measure (toS (rough_state_from_init_state_of S)))
      \<in> lexn less_than 3}", goal_cases)
  case 1
  show ?case by (rule wf_if_measure_f) (auto intro!: wf_lexn wf_less)
next
  case (2 S T) note T = this(1) and ST = this(2)
  let ?S = "rough_state_from_init_state_of S"
  have S: "cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (S0_cdcl\<^sub>W_restart (raw_init_clss (toS ?S))) (toS ?S)"
    using rough_state_from_init_state_of[of S] by auto
  moreover have "cdcl\<^sub>W_restart_stgy (toS (rough_state_from_init_state_of S))
    (toS (rough_state_from_init_state_of T))"
    proof -
      have "\<And>c. rough_state_of (state_of (rough_state_from_init_state_of c)) =
        rough_state_from_init_state_of c"
        using rough_state_from_init_state_of state_of_inverse by fastforce
      then have diff: "do_cdcl\<^sub>W_restart_stgy_step (state_of (rough_state_from_init_state_of S))
        \<noteq> state_of (rough_state_from_init_state_of S)"
        using ST T by (metis (no_types) id_of_I_to_def rough_state_from_init_state_of_inject
          rough_state_from_init_state_of_do_cdcl\<^sub>W_restart_stgy_step')
      have "rough_state_of (do_cdcl\<^sub>W_restart_stgy_step (state_of (rough_state_from_init_state_of S)))
        =  rough_state_from_init_state_of (do_cdcl\<^sub>W_restart_stgy_step' S)"
        by (simp add: id_of_I_to_def rough_state_from_init_state_of_do_cdcl\<^sub>W_restart_stgy_step')
      then show ?thesis
        using do_cdcl\<^sub>W_restart_stgy_step  T  diff unfolding id_of_I_to_def  do_cdcl\<^sub>W_restart_stgy_step by fastforce
    qed
  moreover
    have "cdcl\<^sub>W_restart_all_struct_inv (toS (rough_state_from_init_state_of S))"
      using rough_state_from_init_state_of[of S] by auto
    then have "cdcl\<^sub>W_restart_all_struct_inv (S0_cdcl\<^sub>W_restart (raw_init_clss (toS (rough_state_from_init_state_of S))))"
      by (cases "rough_state_from_init_state_of S")
         (auto simp add: cdcl\<^sub>W_restart_all_struct_inv_def distinct_cdcl\<^sub>W_restart_state_def)
  ultimately show ?case
    using tranclp_cdcl\<^sub>W_restart_stgy_S0_decreasing
    by (auto intro!: cdcl\<^sub>W_restart_stgy_step_decreasing[of _ _ "S0_cdcl\<^sub>W_restart (raw_init_clss (toS ?S))"]
      simp del: cdcl\<^sub>W_restart_measure.simps)
qed

thm do_all_cdcl\<^sub>W_restart_stgy.induct
lemma do_all_cdcl\<^sub>W_restart_stgy_induct:
  "(\<And>S. (do_cdcl\<^sub>W_restart_stgy_step' S \<noteq> S \<Longrightarrow> P (do_cdcl\<^sub>W_restart_stgy_step' S)) \<Longrightarrow> P S) \<Longrightarrow> P a0"
 using do_all_cdcl\<^sub>W_restart_stgy.induct by metis

lemma no_step_cdcl\<^sub>W_restart_stgy_cdcl\<^sub>W_restart_all:
  fixes S :: "'a cdcl\<^sub>W_restart_state_inv_from_init_state"
  shows "no_step cdcl\<^sub>W_restart_stgy (toS (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_restart_stgy S)))"
  apply (induction S rule:do_all_cdcl\<^sub>W_restart_stgy_induct)
  apply (rename_tac S, case_tac "do_cdcl\<^sub>W_restart_stgy_step' S \<noteq> S")
proof -
  fix Sa :: "'a cdcl\<^sub>W_restart_state_inv_from_init_state"
  assume a1: "\<not> do_cdcl\<^sub>W_restart_stgy_step' Sa \<noteq> Sa"
  { fix pp
    have "(if True then Sa else do_all_cdcl\<^sub>W_restart_stgy Sa) = do_all_cdcl\<^sub>W_restart_stgy Sa"
      using a1 by auto
    then have "\<not> cdcl\<^sub>W_restart_stgy (toS (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_restart_stgy Sa))) pp"
      using a1 by (metis (no_types) do_cdcl\<^sub>W_restart_stgy_step_no id_of_I_to_def
        rough_state_from_init_state_of_do_cdcl\<^sub>W_restart_stgy_step' rough_state_of_inverse) }
  then show "no_step cdcl\<^sub>W_restart_stgy (toS (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_restart_stgy Sa)))"
    by fastforce
next
  fix Sa :: "'a cdcl\<^sub>W_restart_state_inv_from_init_state"
  assume a1: "do_cdcl\<^sub>W_restart_stgy_step' Sa \<noteq> Sa
    \<Longrightarrow> no_step cdcl\<^sub>W_restart_stgy (toS (rough_state_from_init_state_of
      (do_all_cdcl\<^sub>W_restart_stgy (do_cdcl\<^sub>W_restart_stgy_step' Sa))))"
  assume a2: "do_cdcl\<^sub>W_restart_stgy_step' Sa \<noteq> Sa"
  have "do_all_cdcl\<^sub>W_restart_stgy Sa = do_all_cdcl\<^sub>W_restart_stgy (do_cdcl\<^sub>W_restart_stgy_step' Sa)"
    by (metis (full_types) do_all_cdcl\<^sub>W_restart_stgy.simps)
  then show "no_step cdcl\<^sub>W_restart_stgy (toS (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_restart_stgy Sa)))"
    using a2 a1 by presburger
qed

lemma do_all_cdcl\<^sub>W_restart_stgy_is_rtranclp_cdcl\<^sub>W_restart_stgy:
  "cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (toS (rough_state_from_init_state_of S))
    (toS (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_restart_stgy S)))"
proof (induction S rule: do_all_cdcl\<^sub>W_restart_stgy_induct)
  case (1 S) note IH = this(1)
  show ?case
    proof (cases "do_cdcl\<^sub>W_restart_stgy_step' S = S")
      case True
      then show ?thesis by simp
    next
      case False
      have f2: "do_cdcl\<^sub>W_restart_stgy_step (id_of_I_to S) = id_of_I_to S \<longrightarrow>
        rough_state_from_init_state_of (do_cdcl\<^sub>W_restart_stgy_step' S)
        = rough_state_of (state_of (rough_state_from_init_state_of S))"
        using rough_state_from_init_state_of_do_cdcl\<^sub>W_restart_stgy_step'
       by (simp add: id_of_I_to_def rough_state_from_init_state_of_do_cdcl\<^sub>W_restart_stgy_step')
      have f3: "do_all_cdcl\<^sub>W_restart_stgy S = do_all_cdcl\<^sub>W_restart_stgy (do_cdcl\<^sub>W_restart_stgy_step' S)"
        by (metis (full_types) do_all_cdcl\<^sub>W_restart_stgy.simps)
      have "cdcl\<^sub>W_restart_stgy (toS (rough_state_from_init_state_of S))
          (toS (rough_state_from_init_state_of (do_cdcl\<^sub>W_restart_stgy_step' S)))
        = cdcl\<^sub>W_restart_stgy (toS (rough_state_of (id_of_I_to S)))
          (toS (rough_state_of (do_cdcl\<^sub>W_restart_stgy_step (id_of_I_to S))))"
        using  rough_state_from_init_state_of_do_cdcl\<^sub>W_restart_stgy_step'
        toS_rough_state_of_state_of_rough_state_from_init_state_of
        by (simp add: id_of_I_to_def rough_state_from_init_state_of_do_cdcl\<^sub>W_restart_stgy_step')
      then show ?thesis
        using f3 f2 IH do_cdcl\<^sub>W_restart_stgy_step by fastforce
    qed
qed

text \<open>Final theorem:\<close>
lemma DPLL_tot_correct:
  assumes
    r: "rough_state_from_init_state_of (do_all_cdcl\<^sub>W_restart_stgy (state_from_init_state_of
      (([], map remdups N, [], 0, None)))) = S" and
    S: "(M', N', U', k, E) = toS S"
  shows "(E \<noteq> Some {#} \<and> satisfiable (set (map mset N)))
    \<or> (E = Some {#} \<and> unsatisfiable (set (map mset N)))"
proof -
  let ?N = "map remdups N"
  have inv: "cdcl\<^sub>W_restart_all_struct_inv (toS ([], map remdups N, [], 0, None))"
    unfolding cdcl\<^sub>W_restart_all_struct_inv_def distinct_cdcl\<^sub>W_restart_state_def distinct_mset_set_def by auto
  then have S0: "rough_state_of (state_of ([], map remdups N, [], 0, None))
    = ([], map remdups N, [], 0, None)" by simp
  have 1: "full cdcl\<^sub>W_restart_stgy (toS ([], ?N, [], 0, None)) (toS S)"
    unfolding full_def apply rule
      using do_all_cdcl\<^sub>W_restart_stgy_is_rtranclp_cdcl\<^sub>W_restart_stgy[of
        "state_from_init_state_of ([], map remdups N, [], 0, None)"] inv
        no_step_cdcl\<^sub>W_restart_stgy_cdcl\<^sub>W_restart_all
        apply (auto simp del: do_all_cdcl\<^sub>W_restart_stgy.simps simp: state_from_init_state_of_inverse
          r[symmetric] comp_def)[]
      using do_all_cdcl\<^sub>W_restart_stgy_is_rtranclp_cdcl\<^sub>W_restart_stgy[of
      "state_from_init_state_of ([], map remdups N, [], 0, None)"] inv
      no_step_cdcl\<^sub>W_restart_stgy_cdcl\<^sub>W_restart_all
      by (force simp: state_from_init_state_of_inverse r["symmetric"] comp_def)
  moreover have 2: "finite (set (map mset ?N))" by auto
  moreover have 3: "distinct_mset_set (set (map mset ?N))"
     unfolding distinct_mset_set_def by auto
  moreover
    have "cdcl\<^sub>W_restart_all_struct_inv (toS S)"
      by (metis (no_types) cdcl\<^sub>W_restart_all_struct_inv_rough_state r
        toS_rough_state_of_state_of_rough_state_from_init_state_of)
    then have cons: "consistent_interp (lits_of_l M')"
      unfolding cdcl\<^sub>W_restart_all_struct_inv_def cdcl\<^sub>W_restart_M_level_inv_def S[symmetric] by auto
  moreover
    have "raw_init_clss (toS ([], ?N, [], 0, None)) = raw_init_clss (toS S)"
      apply (rule rtranclp_cdcl\<^sub>W_restart_stgy_no_more_init_clss)
      using 1 unfolding full_def by (auto simp add: rtranclp_cdcl\<^sub>W_restart_stgy_rtranclp_cdcl\<^sub>W_restart)
    then have N': "mset (map mset ?N) = N'"
      using S[symmetric] by auto
  have "(E \<noteq> Some {#} \<and> satisfiable (set (map mset ?N)))
    \<or> (E = Some {#} \<and> unsatisfiable (set (map mset ?N)))"
    using full_cdcl\<^sub>W_restart_stgy_final_state_conclusive unfolding N' apply rule
        using 1 apply simp
       using 2 apply simp
      using 3 apply simp
     using S[symmetric] N' apply auto[1]
   using S[symmetric] N' cons by (fastforce simp: true_annots_true_cls)
  then show ?thesis by auto
qed

paragraph \<open>The Code\<close>
text \<open>The SML code is skipped in the documentation, but stays to ensure that some version of the
 exported code is working. The only difference between the generated code and the one used here is
 the export of the constructor ConI.\<close>
(*<*)
fun gene where
"gene 0 = [[Pos 0], [Neg 0]]" |
"gene (Suc n) = map (op # (Pos (Suc n))) (gene n) @ map (op # (Neg (Suc n))) (gene n)"

value "gene 1"

export_code do_all_cdcl\<^sub>W_restart_stgy gene in SML
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
  val list_all : ('a -> bool) -> 'a list -> bool
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

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

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
  datatype nat = Zero_nat | Suc of nat
  val equal_nata : nat -> nat -> bool
  val equal_nat : nat HOL.equal
  val less_nat : nat -> nat -> bool
  val linorder_nat : nat Orderings.linorder
  val one_nat : nat
  val plus_nat : nat -> nat -> nat
end = struct

datatype nat = Zero_nat | Suc of nat;

fun equal_nata Zero_nat (Suc x2) = false
  | equal_nata (Suc x2) Zero_nat = false
  | equal_nata (Suc x2) (Suc y2) = equal_nata x2 y2
  | equal_nata Zero_nat Zero_nat = true;

val equal_nat = {equal = equal_nata} : nat HOL.equal;

fun less_eq_nat (Suc m) n = less_nat m n
  | less_eq_nat Zero_nat n = true
and less_nat m (Suc n) = less_eq_nat m n
  | less_nat n Zero_nat = false;

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat Orderings.ord;

val preorder_nat = {ord_preorder = ord_nat} : nat Orderings.preorder;

val order_nat = {preorder_order = preorder_nat} : nat Orderings.order;

val linorder_nat = {order_linorder = order_nat} : nat Orderings.linorder;

val one_nat : nat = Suc Zero_nat;

fun plus_nat (Suc m) n = plus_nat m (Suc n)
  | plus_nat Zero_nat n = n;

end; (*struct Arith*)

structure Option : sig
  val equal_option : 'a HOL.equal -> ('a option) HOL.equal
end = struct

fun equal_optiona A_ NONE (SOME x2) = false
  | equal_optiona A_ (SOME x2) NONE = false
  | equal_optiona A_ (SOME x2) (SOME y2) = HOL.eq A_ x2 y2
  | equal_optiona A_ NONE NONE = true;

fun equal_option A_ = {equal = equal_optiona A_} : ('a option) HOL.equal;

end; (*struct Option*)

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
  datatype ('a, 'b, 'c) ann_lit = Decided of 'a Clausal_Logic.literal * 'b |
    Propagated of 'a Clausal_Logic.literal * 'c
  val equal_ann_lit :
    'a HOL.equal -> 'b HOL.equal -> 'c HOL.equal ->
      ('a, 'b, 'c) ann_lit HOL.equal
  val lits_of : ('a, 'b, 'c) ann_lit list -> 'a Clausal_Logic.literal Set.set
end = struct

datatype ('a, 'b, 'c) ann_lit = Decided of 'a Clausal_Logic.literal * 'b |
  Propagated of 'a Clausal_Logic.literal * 'c;

fun equal_ann_lita A_ B_ C_ (Decided (x11, x12)) (Propagated (x21, x22)) =
  false
  | equal_ann_lita A_ B_ C_ (Propagated (x21, x22)) (Decided (x11, x12)) =
    false
  | equal_ann_lita A_ B_ C_ (Propagated (x21, x22)) (Propagated (y21, y22)) =
    Clausal_Logic.equal_literala A_ x21 y21 andalso HOL.eq C_ x22 y22
  | equal_ann_lita A_ B_ C_ (Decided (x11, x12)) (Decided (y11, y12)) =
    Clausal_Logic.equal_literala A_ x11 y11 andalso HOL.eq B_ x12 y12;

fun equal_ann_lit A_ B_ C_ = {equal = equal_ann_lita A_ B_ C_} :
  ('a, 'b, 'c) ann_lit HOL.equal;

fun lit_of (Decided (x11, x12)) = x11
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

structure CDCL_W_Level : sig
  val get_rev_level :
    'a HOL.equal ->
      ('a, Arith.nat, 'b) Partial_Annotated_Clausal_Logic.ann_lit list ->
        Arith.nat -> 'a Clausal_Logic.literal -> Arith.nat
  val get_maximum_level :
    'a HOL.equal ->
      ('a, Arith.nat, 'b) Partial_Annotated_Clausal_Logic.ann_lit list ->
        'a Clausal_Logic.literal Multiset.multiset -> Arith.nat
end = struct

fun get_rev_level A_ [] uu uv = Arith.Zero_nat
  | get_rev_level A_ (Partial_Annotated_Clausal_Logic.Decided (la, level) :: ls)
    n l =
    (if HOL.eq A_ (Clausal_Logic.atm_of la) (Clausal_Logic.atm_of l) then level
      else get_rev_level A_ ls level l)
  | get_rev_level A_ (Partial_Annotated_Clausal_Logic.Propagated (la, uw) :: ls)
    n l =
    (if HOL.eq A_ (Clausal_Logic.atm_of la) (Clausal_Logic.atm_of l) then n
      else get_rev_level A_ ls n l);

fun get_maximum_level A_ m d =
  Lattices_Big.max Arith.linorder_nat
    (Multiset.set_mset
      (Multiset.plus_multiset (Multiset.single Arith.Zero_nat)
        (Multiset.image_mset (get_rev_level A_ (List.rev m) Arith.Zero_nat)
          d)));

end; (*struct CDCL_W_Level*)

structure Product_Type : sig
  val equal_proda : 'a HOL.equal -> 'b HOL.equal -> 'a * 'b -> 'a * 'b -> bool
  val equal_prod : 'a HOL.equal -> 'b HOL.equal -> ('a * 'b) HOL.equal
end = struct

fun equal_proda A_ B_ (x1, x2) (y1, y2) =
  HOL.eq A_ x1 y1 andalso HOL.eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) HOL.equal;

end; (*struct Product_Type*)

structure DPLL_CDCL_W_Implementation : sig
  val find_first_unused_var :
    'a HOL.equal ->
      ('a Clausal_Logic.literal list) list ->
        'a Clausal_Logic.literal Set.set -> 'a Clausal_Logic.literal option
  val find_first_unit_clause :
    'a HOL.equal ->
      ('a Clausal_Logic.literal list) list ->
        ('a, 'b, 'c) Partial_Annotated_Clausal_Logic.ann_lit list ->
          ('a Clausal_Logic.literal * 'a Clausal_Logic.literal list) option
end = struct

fun is_unit_clause_code A_ l m =
  (case List.filter
          (fn a =>
            not (Set.member A_ (Clausal_Logic.atm_of a)
                  (Set.image Clausal_Logic.atm_of
                    (Partial_Annotated_Clausal_Logic.lits_of m))))
          l
    of [] => NONE
    | [a] =>
      (if List.list_all
            (fn c =>
              Set.member (Clausal_Logic.equal_literal A_)
                (Clausal_Logic.uminus_literal c)
                (Partial_Annotated_Clausal_Logic.lits_of m))
            (List.remove1 (Clausal_Logic.equal_literal A_) a l)
        then SOME a else NONE)
    | _ :: _ :: _ => NONE);

fun is_unit_clause A_ l m = is_unit_clause_code A_ l m;

fun find_first_unused_var A_ (a :: l) m =
  (case List.find
          (fn lit =>
            not (Set.member (Clausal_Logic.equal_literal A_) lit m) andalso
              not (Set.member (Clausal_Logic.equal_literal A_)
                    (Clausal_Logic.uminus_literal lit) m))
          a
    of NONE => find_first_unused_var A_ l m | SOME aa => SOME aa)
  | find_first_unused_var A_ [] uu = NONE;

fun find_first_unit_clause A_ (a :: l) m =
  (case is_unit_clause A_ a m of NONE => find_first_unit_clause A_ l m
    | SOME la => SOME (la, a))
  | find_first_unit_clause A_ [] uu = NONE;

end; (*struct DPLL_CDCL_W_Implementation*)

structure CDCL_W_Implementation : sig
  datatype cdcl_W_state_inv_from_init_state =
    ConI of
      ((Arith.nat, Arith.nat, (Arith.nat Clausal_Logic.literal list))
         Partial_Annotated_Clausal_Logic.ann_lit list *
        ((Arith.nat Clausal_Logic.literal list) list *
          ((Arith.nat Clausal_Logic.literal list) list *
            (Arith.nat * (Arith.nat Clausal_Logic.literal list) option))));
  val gene : Arith.nat -> (Arith.nat Clausal_Logic.literal list) list
  val do_all_cdcl_W_stgy :
    cdcl_W_state_inv_from_init_state -> cdcl_W_state_inv_from_init_state
end = struct

datatype cdcl_W_state_inv =
  Con of
    ((Arith.nat, Arith.nat, (Arith.nat Clausal_Logic.literal list))
       Partial_Annotated_Clausal_Logic.ann_lit list *
      ((Arith.nat Clausal_Logic.literal list) list *
        ((Arith.nat Clausal_Logic.literal list) list *
          (Arith.nat * (Arith.nat Clausal_Logic.literal list) option))));

datatype cdcl_W_state_inv_from_init_state =
  ConI of
    ((Arith.nat, Arith.nat, (Arith.nat Clausal_Logic.literal list))
       Partial_Annotated_Clausal_Logic.ann_lit list *
      ((Arith.nat Clausal_Logic.literal list) list *
        ((Arith.nat Clausal_Logic.literal list) list *
          (Arith.nat * (Arith.nat Clausal_Logic.literal list) option))));

fun gene Arith.Zero_nat =
  [[Clausal_Logic.Pos Arith.Zero_nat], [Clausal_Logic.Neg Arith.Zero_nat]]
  | gene (Arith.Suc n) =
    List.map (fn a => Clausal_Logic.Pos (Arith.Suc n) :: a) (gene n) @
      List.map (fn a => Clausal_Logic.Neg (Arith.Suc n) :: a) (gene n);

fun bt_cut i (Partial_Annotated_Clausal_Logic.Propagated (uu, uv) :: ls) =
  bt_cut i ls
  | bt_cut i (Partial_Annotated_Clausal_Logic.Decided (ka, k) :: ls) =
    (if Arith.equal_nata k (Arith.Suc i)
      then SOME (Partial_Annotated_Clausal_Logic.Decided (ka, k) :: ls)
      else bt_cut i ls)
  | bt_cut i [] = NONE;

fun do_propagate_step A_ s =
  (case s
    of (m, (n, (u, (k, NONE)))) =>
      (case DPLL_CDCL_W_Implementation.find_first_unit_clause A_ (n @ u) m
        of NONE => (m, (n, (u, (k, NONE))))
        | SOME (l, c) =>
          (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: m,
            (n, (u, (k, NONE)))))
    | (m, (n, (u, (k, SOME ah)))) => (m, (n, (u, (k, SOME ah)))));

fun find_conflict A_ m [] = NONE
  | find_conflict A_ m (n :: ns) =
    (if List.list_all
          (fn c =>
            Set.member (Clausal_Logic.equal_literal A_)
              (Clausal_Logic.uminus_literal c)
              (Partial_Annotated_Clausal_Logic.lits_of m))
          n
      then SOME n else find_conflict A_ m ns);

fun do_conflict_step A_ s =
  (case s
    of (m, (n, (u, (k, NONE)))) =>
      (case find_conflict A_ m (n @ u) of NONE => (m, (n, (u, (k, NONE))))
        | SOME a => (m, (n, (u, (k, SOME a)))))
    | (m, (n, (u, (k, SOME ah)))) => (m, (n, (u, (k, SOME ah)))));

fun do_cp_step A_ s = (do_propagate_step A_ o do_conflict_step A_) s;

fun rough_state_from_init_state_of (ConI x) = x;

fun id_of_I_to s = Con (rough_state_from_init_state_of s);

fun rough_state_of (Con x) = x;

fun do_cp_stepa s = Con (do_cp_step Arith.equal_nat (rough_state_of s));

fun do_skip_step
  (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls,
    (n, (u, (k, SOME d))))
  = (if not (List.member (Clausal_Logic.equal_literal Arith.equal_nat) d
              (Clausal_Logic.uminus_literal l)) andalso
          not (List.null d)
      then (ls, (n, (u, (k, SOME d))))
      else (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls,
             (n, (u, (k, SOME d)))))
  | do_skip_step ([], va) = ([], va)
  | do_skip_step (Partial_Annotated_Clausal_Logic.Decided (vd, ve) :: vc, va) =
    (Partial_Annotated_Clausal_Logic.Decided (vd, ve) :: vc, va)
  | do_skip_step (v, (vb, (vd, (vf, NONE)))) = (v, (vb, (vd, (vf, NONE))));

fun maximum_level_code A_ d m =
  CDCL_W_Level.get_maximum_level A_ m (Multiset.Mset d);

fun find_level_decomp A_ m [] d k = NONE
  | find_level_decomp A_ m (l :: ls) d k =
    let
      val (i, j) =
        (CDCL_W_Level.get_rev_level A_ (List.rev m) Arith.Zero_nat l,
          maximum_level_code A_ (d @ ls) m);
    in
      (if Arith.equal_nata i k andalso Arith.less_nat j i then SOME (l, j)
        else find_level_decomp A_ m ls (l :: d) k)
    end;

fun do_backtrack_step A_ (m, (n, (u, (k, SOME d)))) =
  (case find_level_decomp A_ m d [] k of NONE => (m, (n, (u, (k, SOME d))))
    | SOME (l, j) =>
      (case bt_cut j m of NONE => (m, (n, (u, (k, SOME d))))
        | SOME [] => (m, (n, (u, (k, SOME d))))
        | SOME (Partial_Annotated_Clausal_Logic.Decided (_, _) :: ls) =>
          (Partial_Annotated_Clausal_Logic.Propagated (l, d) :: ls,
            (n, (d :: u, (j, NONE))))
        | SOME (Partial_Annotated_Clausal_Logic.Propagated (_, _) :: _) =>
          (m, (n, (u, (k, SOME d))))))
  | do_backtrack_step A_ (v, (vb, (vd, (vf, NONE)))) =
    (v, (vb, (vd, (vf, NONE))));

fun do_resolve_step
  (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls,
    (n, (u, (k, SOME d))))
  = (if List.member (Clausal_Logic.equal_literal Arith.equal_nat) d
          (Clausal_Logic.uminus_literal l) andalso
          Arith.equal_nata
            (maximum_level_code Arith.equal_nat
              (List.remove1 (Clausal_Logic.equal_literal Arith.equal_nat)
                (Clausal_Logic.uminus_literal l) d)
              (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls))
            k
      then (ls, (n, (u, (k, SOME (List.remdups
                                   (Clausal_Logic.equal_literal Arith.equal_nat)
                                   (List.remove1
                                      (Clausal_Logic.equal_literal
Arith.equal_nat)
                                      l c @
                                     List.remove1
                                       (Clausal_Logic.equal_literal
 Arith.equal_nat)
                                       (Clausal_Logic.uminus_literal l) d))))))
      else (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls,
             (n, (u, (k, SOME d)))))
  | do_resolve_step ([], va) = ([], va)
  | do_resolve_step (Partial_Annotated_Clausal_Logic.Decided (vd, ve) :: vc, va)
    = (Partial_Annotated_Clausal_Logic.Decided (vd, ve) :: vc, va)
  | do_resolve_step (v, (vb, (vd, (vf, NONE)))) = (v, (vb, (vd, (vf, NONE))));

fun do_decide_step A_ (m, (n, (u, (k, NONE)))) =
  (case DPLL_CDCL_W_Implementation.find_first_unused_var A_ n
          (Partial_Annotated_Clausal_Logic.lits_of m)
    of NONE => (m, (n, (u, (k, NONE))))
    | SOME l =>
      (Partial_Annotated_Clausal_Logic.Decided (l, Arith.Suc k) :: m,
        (n, (u, (Arith.plus_nat k Arith.one_nat, NONE)))))
  | do_decide_step A_ (v, (vb, (vd, (vf, SOME vh)))) =
    (v, (vb, (vd, (vf, SOME vh))));

fun do_other_step s =
  let
    val t = do_skip_step s;
  in
    (if not (Product_Type.equal_proda
              (List.equal_list
                (Partial_Annotated_Clausal_Logic.equal_ann_lit
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
                    (Option.equal_option
                      (List.equal_list
                        (Clausal_Logic.equal_literal Arith.equal_nat))))))
              t s)
      then t
      else let
             val u = do_resolve_step t;
           in
             (if not (Product_Type.equal_proda
                       (List.equal_list
                         (Partial_Annotated_Clausal_Logic.equal_ann_lit
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
                             (Option.equal_option
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
                                  (Partial_Annotated_Clausal_Logic.equal_ann_lit
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
                                      (Option.equal_option
(List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat))))))
                                v u)
                        then v else do_decide_step Arith.equal_nat v)
                    end)
           end)
  end;

fun do_other_stepa s = Con (do_other_step (rough_state_of s));

fun equal_cdcl_W_state_inv sa s =
  Product_Type.equal_proda
    (List.equal_list
      (Partial_Annotated_Clausal_Logic.equal_ann_lit Arith.equal_nat
        Arith.equal_nat
        (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat))))
    (Product_Type.equal_prod
      (List.equal_list
        (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat)))
      (Product_Type.equal_prod
        (List.equal_list
          (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat)))
        (Product_Type.equal_prod Arith.equal_nat
          (Option.equal_option
            (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat))))))
    (rough_state_of sa) (rough_state_of s);

fun do_full1_cp_step s =
  let
    val sa = do_cp_stepa s;
  in
    (if equal_cdcl_W_state_inv s sa then s else do_full1_cp_step sa)
  end;

fun equal_cdcl_W_state_inv_from_init_state sa s =
  Product_Type.equal_proda
    (List.equal_list
      (Partial_Annotated_Clausal_Logic.equal_ann_lit Arith.equal_nat
        Arith.equal_nat
        (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat))))
    (Product_Type.equal_prod
      (List.equal_list
        (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat)))
      (Product_Type.equal_prod
        (List.equal_list
          (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat)))
        (Product_Type.equal_prod Arith.equal_nat
          (Option.equal_option
            (List.equal_list (Clausal_Logic.equal_literal Arith.equal_nat))))))
    (rough_state_from_init_state_of sa) (rough_state_from_init_state_of s);

fun do_cdcl_W_stgy_step s =
  let
    val t = do_full1_cp_step s;
  in
    (if not (equal_cdcl_W_state_inv t s) then t
      else let
             val a = do_other_stepa t;
           in
             do_full1_cp_step a
           end)
  end;

fun do_cdcl_W_stgy_stepa s =
  ConI (rough_state_of (do_cdcl_W_stgy_step (id_of_I_to s)));

fun do_all_cdcl_W_stgy s =
  let
    val t = do_cdcl_W_stgy_stepa s;
  in
    (if equal_cdcl_W_state_inv_from_init_state t s then s
      else do_all_cdcl_W_stgy t)
  end;

end; (*struct CDCL_W_Implementation*)
\<close>
declare[[ML_print_depth=100]]
ML \<open>
open Clausal_Logic;
open CDCL_W_Implementation;
open Arith;
let
  val N = gene (Suc (Suc (Suc (((Suc Zero_nat))))))
  val f = do_all_cdcl_W_stgy (CDCL_W_Implementation.ConI ([], (N, ([], (Zero_nat, NONE)))))
  in

  f
end
\<close>

(*>*)
end
