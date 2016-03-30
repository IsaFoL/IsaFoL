theory CDCL_W_Implementation
imports DPLL_CDCL_W_Implementation CDCL_W_Termination
begin

notation image_mset (infixr "`#" 90)

type_synonym 'a cdcl\<^sub>W_mark = "'a literal list"
type_synonym cdcl\<^sub>W_marked_level = nat

type_synonym 'v cdcl\<^sub>W_marked_lit = "('v, cdcl\<^sub>W_marked_level, 'v cdcl\<^sub>W_mark) marked_lit"
type_synonym 'v cdcl\<^sub>W_marked_lits = "('v, cdcl\<^sub>W_marked_level, 'v cdcl\<^sub>W_mark) marked_lits"
type_synonym 'v cdcl\<^sub>W_state =
  "'v cdcl\<^sub>W_marked_lits \<times> 'v literal list list \<times> 'v literal list list \<times> nat \<times>
  'v literal list option"

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

abbreviation raw_add_learned_cls where
"raw_add_learned_cls \<equiv> \<lambda>C (M, N, U, S). (M, N, {#C#} + U, S)"

abbreviation raw_remove_cls where
"raw_remove_cls \<equiv> \<lambda>C (M, N, U, S). (M, removeAll_mset C N, removeAll_mset C U, S)"

type_synonym 'v cdcl\<^sub>W_state_inv_st = "('v, nat, 'v literal list) marked_lit list \<times>
  'v literal list list \<times> 'v literal list list \<times> nat \<times> 'v literal list option"

abbreviation "raw_S0_cdcl\<^sub>W N \<equiv> (([], N, [], 0, None):: 'v cdcl\<^sub>W_state_inv_st)"

fun mmset_of_mlit' :: "('v, nat, 'v literal list) marked_lit \<Rightarrow> ('v, nat, 'v clause) marked_lit"
  where
"mmset_of_mlit' (Propagated L C) = Propagated L (mset C)" |
"mmset_of_mlit' (Marked L i) = Marked L i"

lemma lit_of_mmset_of_mlit'[simp]:
  "lit_of (mmset_of_mlit' xa) = lit_of xa"
  by (induction xa) auto

abbreviation trail where
"trail S \<equiv> map mmset_of_mlit' (raw_trail S)"

abbreviation clauses_of_l where
"clauses_of_l \<equiv> \<lambda>L. mset (map mset L)"

global_interpretation state\<^sub>W_ops
  "mset::'v literal list \<Rightarrow> 'v clause"
  "op #" remove1

  clauses_of_l "op @" "\<lambda>L C. L \<in> set C" "op #" "\<lambda>C. remove1_cond (\<lambda>L. mset L = mset C)"

  mset "\<lambda>xs ys. case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))"
  "op #" remove1

  id id

  "\<lambda>(M, _). map mmset_of_mlit' M" "\<lambda>(M, _). hd M"
  "\<lambda>(_, N, _). N"
  "\<lambda>(_, _, U, _). U"
  "\<lambda>(_, _, _, k, _). k"
  "\<lambda>(_, _, _, _, C). C"

  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, S). (M, C # N, S)"
  "\<lambda>C (M, N, U, S). (M, N, C # U, S)"
  "\<lambda>C (M, N, U, S). (M, filter (\<lambda>L. mset L \<noteq> mset C) N, filter (\<lambda>L. mset L \<noteq> mset C) U, S)"
  "\<lambda>(k::nat) (M, N, U, _, D). (M, N, U, k, D)"
  "\<lambda>D (M, N, U, k, _). (M, N, U, k, D)"
  "\<lambda>N. ([], N, [], 0, None)"
  "\<lambda>(_, N, U, _). ([], N, U, 0, None)"
  apply unfold_locales by (auto simp: hd_map comp_def map_tl ac_simps
    union_mset_list mset_map_mset_remove1_cond ex_mset)

lemma mmset_of_mlit'_mmset_of_mlit: "mmset_of_mlit' l = mmset_of_mlit l"
  apply (induct l)
  apply auto
  done

lemma clauses_of_l_filter_removeAll:
  "clauses_of_l [L\<leftarrow>a . mset L \<noteq> mset C] = mset (removeAll (mset C) (map mset a))"
  by (induct a) auto

interpretation state\<^sub>W
  "mset::'v literal list \<Rightarrow> 'v clause"
  "op #" remove1

  clauses_of_l "op @" "\<lambda>L C. L \<in> set C" "op #" "\<lambda>C. remove1_cond (\<lambda>L. mset L = mset C)"

  mset "\<lambda>xs ys. case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))"
  "op #" remove1

  id id

  "\<lambda>(M, _). map mmset_of_mlit' M" "\<lambda>(M, _). hd M"
  "\<lambda>(_, N, _). N"
  "\<lambda>(_, _, U, _). U"
  "\<lambda>(_, _, _, k, _). k"
  "\<lambda>(_, _, _, _, C). C"

  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, S). (M, C # N, S)"
  "\<lambda>C (M, N, U, S). (M, N, C # U, S)"
  "\<lambda>C (M, N, U, S). (M, filter (\<lambda>L. mset L \<noteq> mset C) N, filter (\<lambda>L. mset L \<noteq> mset C) U, S)"
  "\<lambda>(k::nat) (M, N, U, _, D). (M, N, U, k, D)"
  "\<lambda>D (M, N, U, k, _). (M, N, U, k, D)"
  "\<lambda>N. ([], N, [], 0, None)"
  "\<lambda>(_, N, U, _). ([], N, U, 0, None)"
  apply unfold_locales
  apply (rename_tac S, case_tac S)
  by (auto simp: hd_map comp_def map_tl ac_simps clauses_of_l_filter_removeAll
    mmset_of_mlit'_mmset_of_mlit)

global_interpretation conflict_driven_clause_learning\<^sub>W
  "mset::'v literal list \<Rightarrow> 'v clause"
  "op #" remove1

  clauses_of_l "op @" "\<lambda>L C. L \<in> set C" "op #" "\<lambda>C. remove1_cond (\<lambda>L. mset L = mset C)"

  mset "\<lambda>xs ys. case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))"
  "op #" remove1

  id id

  "\<lambda>(M, _). map mmset_of_mlit' M" "\<lambda>(M, _). hd M"
  "\<lambda>(_, N, _). N"
  "\<lambda>(_, _, U, _). U"
  "\<lambda>(_, _, _, k, _). k"
  "\<lambda>(_, _, _, _, C). C"

  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, S). (M, C # N, S)"
  "\<lambda>C (M, N, U, S). (M, N, C # U, S)"
  "\<lambda>C (M, N, U, S). (M, filter (\<lambda>L. mset L \<noteq> mset C) N, filter (\<lambda>L. mset L \<noteq> mset C) U, S)"
  "\<lambda>(k::nat) (M, N, U, _, D). (M, N, U, k, D)"
  "\<lambda>D (M, N, U, k, _). (M, N, U, k, D)"
  "\<lambda>N. ([], N, [], 0, None)"
  "\<lambda>(_, N, U, _). ([], N, U, 0, None)"
  by intro_locales

declare state_simp[simp del] raw_clauses_def[simp] state_eq_def[simp]
notation state_eq (infix "\<sim>" 50)
term reduce_trail_to

lemma reduce_trail_to_map[simp]:
  "reduce_trail_to (map f M1) = reduce_trail_to M1"
  by (rule ext) (auto intro: reduce_trail_to_length)

subsection \<open>CDCL Implementation\<close>
subsubsection \<open>Types and Additional Lemmas\<close>
lemma true_clss_remdups[simp]:
  "I \<Turnstile>s (mset \<circ> remdups) ` N \<longleftrightarrow>  I \<Turnstile>s mset ` N"
  by (simp add: true_clss_def)

lemma satisfiable_mset_remdups[simp]:
  "satisfiable ((mset \<circ> remdups) ` N) \<longleftrightarrow> satisfiable (mset ` N)"
unfolding satisfiable_carac[symmetric] by simp

text \<open>We need some functions to convert between our abstract state @{typ "nat cdcl\<^sub>W_state"} and the
 concrete state @{typ "'v cdcl\<^sub>W_state_inv_st"}.\<close>

abbreviation convertC :: "'a list option \<Rightarrow> 'a multiset option"  where
"convertC \<equiv> map_option mset"

lemma convert_Propagated[elim!]:
  "mmset_of_mlit' z = Propagated L C \<Longrightarrow> (\<exists>C'. z = Propagated L C' \<and> C = mset C')"
  by (cases z) auto

lemma get_rev_level_map_convert:
  "get_rev_level (map mmset_of_mlit' M) n x = get_rev_level M n x"
  by (induction M arbitrary: n rule: marked_lit_list_induct) auto

lemma get_level_map_convert[simp]:
  "get_level (map mmset_of_mlit' M) = get_level M"
  using get_rev_level_map_convert[of "rev M"] by (simp add: rev_map)

lemma get_rev_level_map_mmsetof_mlit[simp]:
  "get_rev_level (map mmset_of_mlit M) = get_rev_level M"
  by (induction M rule: marked_lit_list_induct) (auto intro!: ext)

lemma get_level_map_mmsetof_mlit[simp]:
  "get_level (map mmset_of_mlit M) = get_level M"
  using get_rev_level_map_mmsetof_mlit[of "rev M"] unfolding rev_map by simp

lemma get_maximum_level_map_convert[simp]:
  "get_maximum_level (map mmset_of_mlit' M) D = get_maximum_level M D"
  by (induction D) (auto simp add: get_maximum_level_plus)

lemma get_all_levels_of_marked_map_convert[simp]:
  "get_all_levels_of_marked (map mmset_of_mlit' M) = (get_all_levels_of_marked M)"
  by (induction M rule: marked_lit_list_induct) auto

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
        using reduce_trail_to_length_ne[of S F] IH by (cases S) (auto simp add:)
    qed
qed

text \<open>Definition an abstract type\<close>
typedef 'v  cdcl\<^sub>W_state_inv = "{S::'v cdcl\<^sub>W_state_inv_st. cdcl\<^sub>W_all_struct_inv S}"
  morphisms rough_state_of state_of
proof
  show "([],[], [], 0, None) \<in> {S. cdcl\<^sub>W_all_struct_inv S}"
    by (auto simp add: cdcl\<^sub>W_all_struct_inv_def)
qed

instantiation cdcl\<^sub>W_state_inv :: (type) equal
begin
definition equal_cdcl\<^sub>W_state_inv :: "'v cdcl\<^sub>W_state_inv \<Rightarrow> 'v cdcl\<^sub>W_state_inv \<Rightarrow> bool" where
 "equal_cdcl\<^sub>W_state_inv S S' = (rough_state_of S = rough_state_of S')"
instance
  by standard (simp add: rough_state_of_inject equal_cdcl\<^sub>W_state_inv_def)
end

lemma lits_of_map_convert[simp]: "lits_of_l (map mmset_of_mlit' M) = lits_of_l M"
  by (induction M rule: marked_lit_list_induct) simp_all

lemma undefined_lit_map_convert[iff]:
  "undefined_lit (map mmset_of_mlit' M) L \<longleftrightarrow> undefined_lit M L"
  by (auto simp add: defined_lit_map image_image mmset_of_mlit'_mmset_of_mlit)

lemma true_annot_map_convert[simp]: "map mmset_of_mlit' M \<Turnstile>a N \<longleftrightarrow> M \<Turnstile>a N"
  by (induction M rule: marked_lit_list_induct) (simp_all add: true_annot_def
    mmset_of_mlit'_mmset_of_mlit lits_of_def)

lemma true_annots_map_convert[simp]: "map mmset_of_mlit' M \<Turnstile>as N \<longleftrightarrow> M \<Turnstile>as N"
  unfolding true_annots_def by auto

lemmas propagateE
lemma find_first_unit_clause_some_is_propagate:
  assumes H: "find_first_unit_clause (N @ U) M = Some (L, C)"
  shows "propagate (M, N, U, k, None) (Propagated L C # M, N, U, k, None)"
  using assms
  by (auto dest!: find_first_unit_clause_some intro!: propagate_rule)

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
  "do_propagate_step S \<noteq> S \<Longrightarrow> propagate S (do_propagate_step S)"
  apply (cases S, cases "conflicting S")
  using find_first_unit_clause_some_is_propagate[of "raw_init_clss S" "raw_learned_clss S"]
  by (auto simp add: do_propagate_step_def split: option.splits)

lemma do_propagate_step_option[simp]:
  "conflicting S \<noteq> None \<Longrightarrow> do_propagate_step S = S"
  unfolding do_propagate_step_def by (cases S, cases "conflicting S") auto
thm prod_cases

lemma do_propagate_step_no_step:
  assumes dist: "\<forall>c\<in>set (raw_clauses S). distinct c" and
  prop_step: "do_propagate_step S = S"
  shows "no_step propagate S"
proof (standard, standard)
  fix T
  assume "propagate S T"
  then obtain C L where
    toSS: "conflicting S = None" and
    C: "C \<in> set (raw_clauses S)" and
    L: "L \<in> set C" and
    MC: "raw_trail S \<Turnstile>as CNot (mset (remove1 L C))" and
    T: " T \<sim> raw_cons_trail (Propagated L C) S" and
    undef: "undefined_lit (raw_trail S) L"
    apply (cases S rule: prod_cases5)
    by (elim propagateE) simp
  let ?M = "raw_trail S"
  let ?N = "raw_init_clss S"
  let ?U = "raw_learned_clss S"
  let ?k = "raw_backtrack_lvl S"
  let ?D = "None"
  have S: "S = (?M, ?N, ?U, ?k, ?D)"
    using toSS by (cases S, cases "conflicting S") simp_all

  have "find_first_unit_clause (?N @ ?U) ?M \<noteq> None"
    apply (rule dist find_first_unit_clause_none[of C "?N @ ?U" ?M L, OF _])
        using C dist apply auto[]
       using C apply auto[1]
      using MC apply auto[1]
     using undef apply auto[1]
    using L by auto
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
  "find_conflict M (N@U) = None \<longleftrightarrow> no_step conflict (M, N, U, k, None)"
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
  "do_conflict_step S \<noteq> S \<Longrightarrow> conflict S (do_conflict_step S)"
  apply (cases S, cases "conflicting S")
  unfolding conflict.simps do_conflict_step_def
  by (auto dest!:find_conflict_Some split: option.splits simp: state_eq_def)

lemma do_conflict_step_no_step:
  "do_conflict_step S = S \<Longrightarrow> no_step conflict S"
  apply (cases S, cases "conflicting S")
  unfolding do_conflict_step_def
  using find_conflict_None_no_confl[of "raw_trail S" "raw_init_clss S" "raw_learned_clss S"
      "raw_backtrack_lvl S"]
  by (auto split: option.split elim: conflictE)

lemma do_conflict_step_option[simp]:
  "conflicting S \<noteq> None \<Longrightarrow> do_conflict_step S = S"
  unfolding do_conflict_step_def by (cases S, cases "conflicting S") auto

lemma do_conflict_step_conflicting[dest]:
  "do_conflict_step S \<noteq> S \<Longrightarrow> conflicting (do_conflict_step S) \<noteq> None"
  unfolding do_conflict_step_def by (cases S, cases "conflicting S") (auto split: option.splits)

definition do_cp_step where
"do_cp_step S =
  (do_propagate_step o do_conflict_step) S"

lemma cp_step_is_cdcl\<^sub>W_cp:
  assumes H: "do_cp_step S \<noteq> S"
  shows "cdcl\<^sub>W_cp S (do_cp_step S)"
proof -
  show ?thesis
  proof (cases "do_conflict_step S \<noteq> S")
    case True
    then have "do_propagate_step (do_conflict_step S) = do_conflict_step S"
      by auto
    then show ?thesis
      by (auto simp add: do_conflict_step do_conflict_step_conflicting do_cp_step_def True)
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
        let ?S = "S"
        let ?T = "(do_propagate_step S)"
        let ?U = "(do_conflict_step (do_propagate_step S))"
        have propa: "propagate S ?T" using False do_propgate_step by blast
        moreover have ns: "no_step conflict S" using confl do_conflict_step_no_step by blast
        ultimately show ?thesis
          using cdcl\<^sub>W_cp.intros(2)[of ?S ?T] confl unfolding do_cp_step_def by auto
      qed
  qed
qed

lemma do_cp_step_eq_no_prop_no_confl:
  "do_cp_step S = S \<Longrightarrow> do_conflict_step S = S \<and> do_propagate_step S = S"
  by (cases S, cases "raw_conflicting S")
    (auto simp add: do_conflict_step_def do_propagate_step_def do_cp_step_def split: option.splits)

lemma no_cdcl\<^sub>W_cp_iff_no_propagate_no_conflict:
  "no_step cdcl\<^sub>W_cp S \<longleftrightarrow> no_step propagate S \<and> no_step conflict S"
  by (auto simp: cdcl\<^sub>W_cp.simps)

lemma do_cp_step_eq_no_step:
  assumes
    H: "do_cp_step S = S" and "
    \<forall>c \<in> set (raw_init_clss S @ raw_learned_clss S). distinct c"
  shows "no_step cdcl\<^sub>W_cp S"
  unfolding no_cdcl\<^sub>W_cp_iff_no_propagate_no_conflict
  using assms apply (cases S, cases "conflicting S")
  using do_propagate_step_no_step[of S]
  by (auto dest!: do_cp_step_eq_no_prop_no_confl[simplified] do_conflict_step_no_step
    split: option.splits)

lemma cdcl\<^sub>W_cp_cdcl\<^sub>W_st: "cdcl\<^sub>W_cp S S' \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S S'"
  by (simp add: cdcl\<^sub>W_cp_tranclp_cdcl\<^sub>W tranclp_into_rtranclp)

lemma cdcl\<^sub>W_all_struct_inv_rough_state[simp]: "cdcl\<^sub>W_all_struct_inv (rough_state_of S)"
  using rough_state_of by auto

lemma [simp]: "cdcl\<^sub>W_all_struct_inv S \<Longrightarrow> rough_state_of (state_of S) = S"
  by (simp add: state_of_inverse)

lemma rough_state_of_state_of_do_cp_step[simp]:
  "rough_state_of (state_of (do_cp_step (rough_state_of S))) = do_cp_step (rough_state_of S)"
proof -
  have "cdcl\<^sub>W_all_struct_inv (do_cp_step (rough_state_of S))"
    apply (cases "do_cp_step (rough_state_of S) = (rough_state_of S)")
      apply simp
    using cp_step_is_cdcl\<^sub>W_cp[of "rough_state_of S"] cdcl\<^sub>W_all_struct_inv_rough_state[of S]
    cdcl\<^sub>W_cp_cdcl\<^sub>W_st rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
  then show ?thesis by auto
qed

paragraph \<open>Skip\<close>
fun do_skip_step :: "'v cdcl\<^sub>W_state_inv_st \<Rightarrow> 'v cdcl\<^sub>W_state_inv_st" where
"do_skip_step (Propagated L C # Ls,N,U,k, Some D) =
  (if -L \<notin> set D \<and> D \<noteq> []
  then (Ls, N, U, k, Some D)
  else (Propagated L C #Ls, N, U, k, Some D))" |
"do_skip_step S = S"

lemma do_skip_step:
  "do_skip_step S \<noteq> S \<Longrightarrow> skip S (do_skip_step S)"
  apply (induction S rule: do_skip_step.induct)
  by (auto simp add: skip.simps)

lemma do_skip_step_no:
  "do_skip_step S = S \<Longrightarrow> no_step skip S"
  by (induction S rule: do_skip_step.induct)
     (auto simp add: other split: if_split_asm elim!: skipE)

lemma do_skip_step_trail_is_None[iff]:
  "do_skip_step S = (a, b, c, d, None) \<longleftrightarrow> S = (a, b, c, d, None)"
  by (cases S rule: do_skip_step.cases) auto

paragraph \<open>Resolve\<close>
fun maximum_level_code:: "'a literal list \<Rightarrow> ('a, nat, 'b) marked_lit list \<Rightarrow> nat"
  where
"maximum_level_code [] _ = 0" |
"maximum_level_code (L # Ls) M = max (get_level M L) (maximum_level_code Ls M)"

lemma maximum_level_code_eq_get_maximum_level[simp]:
  "maximum_level_code D M = get_maximum_level M (mset D)"
  by (induction D) (auto simp add: get_maximum_level_plus)

lemma [code]:
  fixes M :: "('a::{type}, nat, 'b) marked_lit list"
  shows "get_maximum_level M (mset D) = maximum_level_code D M"
  by simp

fun do_resolve_step :: "'v cdcl\<^sub>W_state_inv_st \<Rightarrow> 'v cdcl\<^sub>W_state_inv_st" where
"do_resolve_step (Propagated L C # Ls, N, U, k, Some D) =
  (if -L \<in> set D \<and> maximum_level_code (remove1 (-L) D) (Propagated L C # Ls) = k
  then (Ls, N, U, k, Some (remdups (remove1 L C @ remove1 (-L) D)))
  else (Propagated L C # Ls, N, U, k, Some D))" |
"do_resolve_step S = S"

lemma do_resolve_step:
  "cdcl\<^sub>W_all_struct_inv S \<Longrightarrow> do_resolve_step S \<noteq> S
  \<Longrightarrow> resolve S (do_resolve_step S)"
proof (induction S rule: do_resolve_step.induct)
  case (1 L C M N U k D)
  then have
    LD: "- L \<in> set D" and
    M: "maximum_level_code (remove1 (-L) D) (Propagated L C # M) = k"
    by (cases "mset D - {#- L#} = {#}",
        auto dest!: get_maximum_level_exists_lit_of_max_level[of _ "Propagated L C # M"]
        split: if_split_asm)+
  have "every_mark_is_a_conflict (Propagated L C # M, N, U, k, Some D)"
    using 1(1) unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def by fast
  then have LC: "L \<in> set C" by fastforce
  then obtain C' where C: "mset C = C' + {#L#}"
    by (metis add.commute in_multiset_in_set insert_DiffM)
  obtain D' where D: "mset D = D' + {#-L#}"
    using \<open>- L \<in> set D\<close> by (metis add.commute in_multiset_in_set insert_DiffM)
  have D'L:  "D' + {#- L#} - {#-L#} = D'" by (auto simp add: multiset_eq_iff)

  have CL: "mset C - {#L#} + {#L#} = mset C" using \<open>L \<in> set C\<close> by (auto simp add: multiset_eq_iff)
  have max: "get_maximum_level (Propagated L (C' + {#L#}) # map mmset_of_mlit' M) D' = k"
    using M[simplified] unfolding maximum_level_code_eq_get_maximum_level C[symmetric] CL
    by (metis D D'L get_maximum_level_map_convert list.simps(9) mmset_of_mlit'.simps(1))
  have "distinct_mset (mset C)" and "distinct_mset (mset D)"
    using \<open>cdcl\<^sub>W_all_struct_inv (Propagated L C # M, N, U, k, Some D)\<close>
    unfolding cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def
    by auto
  then have conf: "(mset C - {#L#}) #\<union> (mset D - {#- L#}) =
    remdups_mset (mset C - {#L#} + (mset D - {#- L#}))"
    by (auto simp: distinct_mset_rempdups_union_mset)
  show ?case
    apply (rule resolve_rule)
    using LC LD max M conf C D by (auto simp: subset_mset.sup.commute)
qed auto

lemma do_resolve_step_no:
  "do_resolve_step S = S \<Longrightarrow> no_step resolve S"
  apply (cases S; cases "(raw_trail S)"; cases "raw_conflicting S")
  by (auto
    elim!: resolveE  split: if_split_asm
    dest!: union_single_eq_member
    simp del: in_multiset_in_set get_maximum_level_map_convert
    simp: get_maximum_level_map_convert[symmetric] do_resolve_step)

lemma rough_state_of_state_of_resolve[simp]:
  "cdcl\<^sub>W_all_struct_inv S \<Longrightarrow> rough_state_of (state_of (do_resolve_step S)) = do_resolve_step S"
  apply (rule state_of_inverse)
  apply (cases "do_resolve_step S = S")
   apply simp
  by (blast dest: other resolve bj do_resolve_step cdcl\<^sub>W_all_struct_inv_inv)

lemma do_resolve_step_trail_is_None[iff]:
  "do_resolve_step S = (a, b, c, d, None) \<longleftrightarrow> S = (a, b, c, d, None)"
  by (cases S rule: do_resolve_step.cases) auto

paragraph \<open>Backjumping\<close>
fun find_level_decomp where
"find_level_decomp M [] D k = None" |
"find_level_decomp M (L # Ls) D k =
  (case (get_level M L, maximum_level_code (D @ Ls) M) of
    (i, j) \<Rightarrow> if i = k \<and> j < i then Some (L, j) else find_level_decomp M Ls (L#D) k
  )"

lemma find_level_decomp_some:
  assumes "find_level_decomp M Ls D k = Some (L, j)"
  shows "L \<in> set Ls \<and> get_maximum_level M (mset (remove1 L (Ls @ D))) = j \<and> get_level M L = k"
  using assms
proof (induction Ls arbitrary: D)
  case Nil
  then show ?case by simp
next
  case (Cons L' Ls) note IH = this(1) and H = this(2)
  (* heavily modified sledgehammer proof *)
  def find \<equiv> "(if get_level M L' \<noteq> k \<or> \<not> get_maximum_level M (mset D + mset Ls) < get_level M L'
    then find_level_decomp M Ls (L' # D) k
    else Some (L', get_maximum_level M (mset D + mset Ls)))"
  have a1: "\<And>D. find_level_decomp M Ls D k = Some (L, j) \<Longrightarrow>
     L \<in> set Ls \<and> get_maximum_level M (mset Ls + mset D - {#L#}) = j \<and> get_level M L = k"
    using IH by simp
  have a2: "find = Some (L, j)"
    using H unfolding find_def by (auto split: if_split_asm)
  { assume "Some (L', get_maximum_level M (mset D + mset Ls)) \<noteq> find"
    then have f3: "L \<in> set Ls" and "get_maximum_level M (mset Ls + mset (L' # D) - {#L#}) = j"
      using a1 IH a2 unfolding find_def by meson+
    moreover then have "mset Ls + mset D - {#L#} + {#L'#} = {#L'#} + mset D + (mset Ls - {#L#})"
      by (auto simp: ac_simps multiset_eq_iff Suc_leI)
    ultimately have f4: "get_maximum_level M (mset Ls + mset D - {#L#} + {#L'#}) = j"
      by (metis add.commute diff_union_single_conv in_multiset_in_set mset.simps(2))
  } note f4 = this
  have "{#L'#} + (mset Ls + mset D) = mset Ls + (mset D + {#L'#})"
      by (auto simp: ac_simps)
  then have
    "(L = L' \<longrightarrow> get_maximum_level M (mset Ls + mset D) = j \<and> get_level M L' = k)" and
    "(L \<noteq> L' \<longrightarrow> L \<in> set Ls \<and> get_maximum_level M (mset Ls + mset D - {#L#} + {#L'#}) = j \<and>
      get_level M L = k)"
    using f4 a2 a1[of "L' # D"] unfolding find_def by (metis (no_types) add_diff_cancel_left'
      mset.simps(2) option.inject prod.inject union_commute)+
  then show ?case by simp
qed

lemma find_level_decomp_none:
  assumes "find_level_decomp M Ls E k = None" and "mset (L#D) = mset (Ls @ E)"
  shows "\<not>(L \<in> set Ls \<and> get_maximum_level M (mset D) < k \<and> k = get_level M L)"
  using assms
proof (induction Ls arbitrary: E L D)
  case Nil
  then show ?case by simp
next
  case (Cons L' Ls) note IH = this(1) and find_none = this(2) and LD = this(3)
  have "mset D + {#L'#} = mset E + (mset Ls + {#L'#})  \<Longrightarrow> mset D = mset E + mset Ls"
    by (metis add_right_imp_eq union_assoc)
  then show ?case
    using find_none IH[of "L' # E" L D] LD by (auto simp add: ac_simps split: if_split_asm)
qed

fun bt_cut where
"bt_cut i (Propagated _ _ # Ls) = bt_cut i Ls" |
"bt_cut i (Marked K k # Ls) = (if k = Suc i then Some (Marked K k # Ls) else bt_cut i Ls)" |
"bt_cut i [] = None"

lemma bt_cut_some_decomp:
  "bt_cut i M = Some M' \<Longrightarrow> \<exists>K M2 M1. M = M2 @ M' \<and> M' = Marked K (i+1) # M1"
  by (induction i M rule: bt_cut.induct) (auto split: if_split_asm)

lemma bt_cut_not_none: "M = M2 @ Marked K (Suc i) # M' \<Longrightarrow> bt_cut i M \<noteq> None"
  by (induction M2 arbitrary: M rule: marked_lit_list_induct) auto

lemma get_all_marked_decomposition_ex:
  "\<exists>N. (Marked K (Suc i) # M', N) \<in> set (get_all_marked_decomposition (M2@Marked K (Suc i) # M'))"
  apply (induction M2 rule: marked_lit_list_induct)
    apply auto[2]
  by (rename_tac L m xs,  case_tac "get_all_marked_decomposition (xs @ Marked K (Suc i) # M')")
  auto

lemma bt_cut_in_get_all_marked_decomposition:
  "bt_cut i M = Some M' \<Longrightarrow> \<exists>M2. (M', M2) \<in> set (get_all_marked_decomposition M)"
  by (auto dest!: bt_cut_some_decomp simp add: get_all_marked_decomposition_ex)

fun do_backtrack_step where
"do_backtrack_step (M, N, U, k, Some D) =
  (case find_level_decomp M D [] k of
    None \<Rightarrow> (M, N, U, k, Some D)
  | Some (L, j) \<Rightarrow>
    (case bt_cut j M of
      Some (Marked _ _ # Ls) \<Rightarrow> (Propagated L D # Ls, N, D # U, j, None)
    | _ \<Rightarrow> (M, N, U, k, Some D))
  )" |
"do_backtrack_step S = S"

lemma get_all_marked_decomposition_map_convert:
  "(get_all_marked_decomposition (map mmset_of_mlit' M)) =
    map (\<lambda>(a, b). (map mmset_of_mlit' a, map mmset_of_mlit' b)) (get_all_marked_decomposition M)"
  apply (induction M rule: marked_lit_list_induct)
    apply simp
  by (rename_tac L l xs, case_tac "get_all_marked_decomposition xs"; auto)+

lemma do_backtrack_step:
  assumes
    db: "do_backtrack_step S \<noteq> S" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "backtrack S (do_backtrack_step S)"
  proof (cases S, cases "raw_conflicting S", goal_cases)
    case (1 M N U k E)
    then show ?case using db by auto
  next
    case (2 M N U k E C) note S = this(1) and confl = this(2)
    have E: "E = Some C" using S confl by auto

    obtain L j where fd: "find_level_decomp M C [] k = Some (L, j)"
      using db unfolding S E  by (cases C) (auto split: if_split_asm option.splits)
    have
      "L \<in> set C" and
      j: "get_maximum_level M (mset (remove1 L C)) = j" and
      levL: "get_level M L = k"
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
    have "get_all_levels_of_marked (map mmset_of_mlit' M) = rev [1..<Suc k]"
      using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def S by auto
    from arg_cong[OF this, of "\<lambda>a. Suc j \<in> set a"] have "j \<le> k" unfolding c by auto
    have max_l_j: "maximum_level_code C' M = j"
      using db fd M\<^sub>2 C unfolding S E by (auto
          split: option.splits list.splits marked_lit.splits
          dest!: find_level_decomp_some)[1]
    have "get_maximum_level M (mset C) \<ge> k"
      using \<open>L \<in> set C\<close> levL get_maximum_level_ge_get_level by (metis set_mset_mset)
    moreover have "get_maximum_level M (mset C) \<le> k"
      using get_maximum_level_exists_lit_of_max_level[of "mset C" M] inv
        cdcl\<^sub>W_M_level_inv_get_level_le_backtrack_lvl[of S]
      unfolding C cdcl\<^sub>W_all_struct_inv_def S by (auto dest: sym[of "get_level _ _"])
    ultimately have "get_maximum_level M (mset C) = k" by auto

    obtain M2 where M2: "(M\<^sub>2, M2) \<in> set (get_all_marked_decomposition M)"
      using bt_cut_in_get_all_marked_decomposition[OF M\<^sub>2] by metis
    have decomp:
      "(Marked K (Suc (get_maximum_level M (remove1_mset L (mset C)))) # (map mmset_of_mlit' M1),
      (map mmset_of_mlit' M2)) \<in>
      set (get_all_marked_decomposition (map mmset_of_mlit' M))"
      using imageI[of _ _ "\<lambda>(a, b). (map mmset_of_mlit' a, map mmset_of_mlit' b)", OF M2] j
      unfolding S E M1 by (auto simp add: get_all_marked_decomposition_map_convert)
    have red: "(reduce_trail_to (map mmset_of_mlit' M1)
      (M, N, C # U, get_maximum_level M (remove1_mset L (mset C)), None))
      = (M1, N, C # U, get_maximum_level M (remove1_mset L (mset C)), None)"
     using  M2 M1 by (auto simp: reduce_trail_to)
    show ?case
      apply (rule backtrack_rule)
      using M\<^sub>2 fd confl \<open>L \<in> set C\<close> j decomp levL \<open>get_maximum_level M (mset C) = k\<close>
      unfolding S E M1 apply (auto simp: mset_map)[6]
      unfolding CDCL_W_Implementation.state_eq_def
      using M\<^sub>2 fd confl \<open>L \<in> set C\<close> j decomp levL \<open>get_maximum_level M (mset C) = k\<close> red
      unfolding S E M1
      by auto
qed

lemma map_eq_list_length:
  "map f L = L' \<Longrightarrow> length L = length L'"
  by auto

lemma map_mmset_of_mlit_eq_cons:
  assumes "map mmset_of_mlit' M = a @ c"
  obtains a' c' where
     "M = a' @  c'" and
     "a = map mmset_of_mlit' a'" and
     "c = map mmset_of_mlit' c'"
  using that[of "take (length a) M" "drop (length a) M"]
  assms by (metis append_eq_conv_conj append_take_drop_id drop_map take_map)

lemma do_backtrack_step_no:
  assumes
    db: "do_backtrack_step S = S" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "no_step backtrack S"
proof (rule ccontr, cases S, cases "conflicting S", goal_cases)
  case 1
  then show ?case using db by (auto split: option.splits elim: backtrackE)
next
  case (2 M N U k E C) note bt = this(1) and S = this(2) and confl = this(3)
  obtain K j M1 M2 L D where
    CE: "raw_conflicting S = Some D" and
    LD: "L \<in># mset D" and
    decomp: "(Marked K (Suc j) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))" and
    levL: "get_level (raw_trail S) L = raw_backtrack_lvl S"  and
    k: "get_level (raw_trail S) L = get_maximum_level (raw_trail S) (mset D)" and
    j: "get_maximum_level (raw_trail S) (remove1_mset L (mset D)) \<equiv> j" and
    undef: "undefined_lit M1 L"
    using bt apply clarsimp
    apply (elim backtrack_levE)
      using inv unfolding  cdcl\<^sub>W_all_struct_inv_def apply fast
    apply (cases S)
    by (auto simp add: get_all_marked_decomposition_map_convert)
(*     levL: "get_level M L = get_maximum_level M (D + {#L#})" and
    k: "k = get_maximum_level M (D + {#L#})" and
    j: "j = get_maximum_level M D" and
    CE: "convertC E = Some (D + {#L#})" and
    decomp: "(z # M1, b) \<in> set (get_all_marked_decomposition M)" and
    z: "Marked K (Suc j) = mmset_of_mlit' z" using bt unfolding S
      by (auto split: option.splits elim!: backtrackE
        simp: get_all_marked_decomposition_map_convert reduce_trail_to
        dest!: get_all_marked_decomposition_exists_prepend) *)
  obtain c where c: "trail S = c @ M2 @ Marked K (Suc j) # M1"
    using decomp by blast
  have "get_all_levels_of_marked (trail S) = rev [1..<Suc k]"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def S by auto
  from arg_cong[OF this, of "\<lambda>a. Suc j \<in> set a"] have "k > j"
    unfolding c by (auto simp: get_all_marked_decomposition_map_convert)
  have [simp]: "L \<in> set D"
    using LD by auto
  have CD: "C = mset D"
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

  obtain c' M1' where cM: "M = c' @ Marked K (Suc j) # M1'"
    apply (rule map_mmset_of_mlit_eq_cons[of M "c @ M2" "Marked K (Suc j) # M1"])
      using c S apply simp
    apply (rule map_mmset_of_mlit_eq_cons[of _ "[Marked K (Suc j)]" " M1"])
     apply auto[]
    apply (rename_tac a b' aa b, case_tac aa)
     apply auto[]
    apply (rename_tac a b' aa b, case_tac aa)
    by auto
  have btc_none: "bt_cut j M \<noteq> None"
    apply (rule bt_cut_not_none[of M ])
    using cM by simp
  show ?case using db unfolding S  E
    by (auto split: option.splits list.splits marked_lit.splits
      simp add: fd_some  L' j' btc_none
      dest: bt_cut_some_decomp)
qed

lemma rough_state_of_state_of_backtrack[simp]:
  assumes inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "rough_state_of (state_of (do_backtrack_step S))= do_backtrack_step S"
proof (rule state_of_inverse)
  have f2: "backtrack S (do_backtrack_step S) \<or> do_backtrack_step S = S"
    using do_backtrack_step inv by blast
  have "\<And>p. \<not> cdcl\<^sub>W_o S p \<or> cdcl\<^sub>W_all_struct_inv p"
    using inv cdcl\<^sub>W_all_struct_inv_inv other by blast
  then have "do_backtrack_step S = S \<or> cdcl\<^sub>W_all_struct_inv (do_backtrack_step S)"
    using f2 inv cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros by blast
  then show "do_backtrack_step S \<in> {S. cdcl\<^sub>W_all_struct_inv S}"
    using inv by  fastforce
qed

paragraph \<open>Decide\<close>
fun do_decide_step where
"do_decide_step (M, N, U, k, None) =
  (case find_first_unused_var N (lits_of_l M) of
    None \<Rightarrow> (M, N, U, k, None)
  | Some L \<Rightarrow> (Marked L (Suc k) # M, N, U, k+1, None))" |
"do_decide_step S = S"

lemma do_decide_step:
  fixes S :: "'v cdcl\<^sub>W_state_inv_st"
  assumes  "do_decide_step S \<noteq> S"
  shows " decide S (do_decide_step S)"
  using assms
  apply (cases S, cases "conflicting S")
  defer
  apply (auto split: option.splits simp add: decide.simps Marked_Propagated_in_iff_in_lits_of_l
          dest: find_first_unused_var_undefined find_first_unused_var_Some
          intro:)[1]
proof -
  fix a :: "('v, nat, 'v literal list) marked_lit list" and
        b :: "'v literal list list" and  c :: "'v literal list list" and
        d :: nat and e :: "'v literal list option"
  {
    fix a :: "('v, nat, 'v literal list) marked_lit list" and
        b :: "'v literal list list" and  c :: "'v literal list list" and
        d :: nat and x2 :: "'v literal" and m :: "'v literal list"
    assume a1: "m \<in> set b"
    assume "x2 \<in> set m"
    then have f2: "atm_of x2 \<in> atms_of (mset m)"
      by simp
    have "\<And>f. (f m::'v clause) \<in> f ` set b"
      using a1 by blast
    then have "\<And>f. (atms_of (f m)::'v set) \<subseteq> atms_of_ms (f ` set b)"
      by simp
    then have "\<And>n f. (n::'v) \<in> atms_of_ms (f ` set b) \<or> n \<notin> atms_of (f m)"
      by (meson contra_subsetD)
    then have "atm_of x2 \<in> atms_of_ms (mset ` set b)"
      using f2 by blast
  } note H = this
  {
    fix m :: "'v literal list" and x2
    have "m \<in> set b \<Longrightarrow> x2 \<in> set m \<Longrightarrow> x2 \<notin> lits_of_l a \<Longrightarrow> - x2 \<notin> lits_of_l a \<Longrightarrow>
      \<exists>aa\<in>set b. \<not> atm_of ` set aa \<subseteq> atm_of ` lits_of_l a"
      by (meson atm_of_in_atm_of_set_in_uminus contra_subsetD rev_image_eqI)
  } note H' = this

  assume  "do_decide_step S \<noteq> S" and
     "S = (a, b, c, d, e)" and
     "conflicting S = None"
  then show "decide S (do_decide_step S)"
    using H H' by (auto split: option.splits simp: lits_of_def decide.simps 
      Marked_Propagated_in_iff_in_lits_of_l
      dest!: find_first_unused_var_Some)
qed

lemma mmset_of_mlit'_eq_Marked[iff]: "mmset_of_mlit' z = Marked x k \<longleftrightarrow> z = Marked x k"
  by (cases z) auto

lemma do_decide_step_no:
  "do_decide_step S = S \<Longrightarrow> no_step decide S"
  apply (cases S, cases "conflicting S")
  (* TODO Tune proof *)
  apply (auto simp: atms_of_ms_mset_unfold  Marked_Propagated_in_iff_in_lits_of_l lits_of_def
      dest!: atm_of_in_atm_of_set_in_uminus
      elim!: decideE
      split: option.splits)+
using atm_of_eq_atm_of by blast

lemma rough_state_of_state_of_do_decide_step[simp]:
  "cdcl\<^sub>W_all_struct_inv S \<Longrightarrow> rough_state_of (state_of (do_decide_step S)) = do_decide_step S"
proof (subst state_of_inverse, goal_cases)
  case 1
  then show ?case
    by (cases "do_decide_step S = S")
      (auto dest: do_decide_step decide other intro: cdcl\<^sub>W_all_struct_inv_inv)
qed simp

lemma rough_state_of_state_of_do_skip_step[simp]:
  "cdcl\<^sub>W_all_struct_inv S \<Longrightarrow> rough_state_of (state_of (do_skip_step S)) = do_skip_step S"
  apply (subst state_of_inverse, cases "do_skip_step S = S")
   apply simp
  by (blast dest: other skip bj do_skip_step cdcl\<^sub>W_all_struct_inv_inv)+

subsubsection \<open>Code generation\<close>
paragraph \<open>Type definition\<close>
text \<open>There are two invariants: one while applying conflict and propagate and one for the other
 rules\<close>

declare rough_state_of_inverse[simp add]
definition Con where
  "Con xs = state_of (if cdcl\<^sub>W_all_struct_inv xs then xs else ([], [], [], 0, None))"

lemma [code abstype]:
 "Con (rough_state_of S) = S"
  using rough_state_of[of S] unfolding Con_def by simp

definition do_cp_step' where
"do_cp_step' S = state_of (do_cp_step (rough_state_of S))"

typedef 'v cdcl\<^sub>W_state_inv_from_init_state = "{S::'v cdcl\<^sub>W_state_inv_st. cdcl\<^sub>W_all_struct_inv S
  \<and> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (raw_S0_cdcl\<^sub>W (raw_init_clss S)) S}"
  morphisms rough_state_from_init_state_of state_from_init_state_of
proof
  show "([],[], [], 0, None) \<in> {S. cdcl\<^sub>W_all_struct_inv S
    \<and> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (raw_S0_cdcl\<^sub>W (raw_init_clss S)) S}"
    by (auto simp add: cdcl\<^sub>W_all_struct_inv_def)
qed

instantiation cdcl\<^sub>W_state_inv_from_init_state :: (type) equal
begin
definition equal_cdcl\<^sub>W_state_inv_from_init_state :: "'v cdcl\<^sub>W_state_inv_from_init_state \<Rightarrow>
  'v cdcl\<^sub>W_state_inv_from_init_state \<Rightarrow> bool" where
 "equal_cdcl\<^sub>W_state_inv_from_init_state S S' \<longleftrightarrow>
   (rough_state_from_init_state_of S = rough_state_from_init_state_of S')"
instance
  by standard (simp add: rough_state_from_init_state_of_inject
    equal_cdcl\<^sub>W_state_inv_from_init_state_def)
end

definition ConI where
  "ConI S = state_from_init_state_of (if cdcl\<^sub>W_all_struct_inv S
    \<and> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (raw_S0_cdcl\<^sub>W (raw_init_clss S)) S then S else ([], [], [], 0, None))"

lemma [code abstype]:
  "ConI (rough_state_from_init_state_of S) = S"
  using rough_state_from_init_state_of[of S] unfolding ConI_def
  by (simp add: rough_state_from_init_state_of_inverse)

definition id_of_I_to :: "'v cdcl\<^sub>W_state_inv_from_init_state \<Rightarrow> 'v cdcl\<^sub>W_state_inv" where
"id_of_I_to S = state_of (rough_state_from_init_state_of S)"

lemma [code abstract]:
  "rough_state_of (id_of_I_to S) = rough_state_from_init_state_of S"
  unfolding id_of_I_to_def using rough_state_from_init_state_of[of S] by auto

paragraph \<open>Conflict and Propagate\<close>
function do_full1_cp_step :: "'v cdcl\<^sub>W_state_inv \<Rightarrow> 'v cdcl\<^sub>W_state_inv" where
"do_full1_cp_step S =
  (let S' = do_cp_step' S in
   if S = S' then S else do_full1_cp_step S')"
by auto
termination
proof (relation "{(T', T). (rough_state_of T', rough_state_of T) \<in> {(S', S).
  (S', S) \<in> {(S', S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_cp S S'}}}", goal_cases)
  case 1
  show ?case
    using wf_if_measure_f[OF wf_if_measure_f[OF cdcl\<^sub>W_cp_wf_all_inv, of ], of rough_state_of] .
next
  case (2 S' S)
  then show ?case
    unfolding do_cp_step'_def
    apply simp
    by (metis cp_step_is_cdcl\<^sub>W_cp rough_state_of_inverse)
qed

lemma do_full1_cp_step_fix_point_of_do_full1_cp_step:
  "do_cp_step(rough_state_of (do_full1_cp_step S)) = rough_state_of (do_full1_cp_step S)"
  by (rule do_full1_cp_step.induct[of "\<lambda>S. do_cp_step(rough_state_of (do_full1_cp_step S))
       = rough_state_of (do_full1_cp_step S)"])
    (metis (full_types) do_full1_cp_step.elims rough_state_of_state_of_do_cp_step do_cp_step'_def)

lemma in_clauses_rough_state_of_is_distinct:
  "c\<in>set (raw_init_clss (rough_state_of S) @ raw_learned_clss (rough_state_of S)) \<Longrightarrow> distinct c"
  apply (cases "rough_state_of S")
  using rough_state_of[of S] by (auto simp add: distinct_mset_set_distinct cdcl\<^sub>W_all_struct_inv_def
    distinct_cdcl\<^sub>W_state_def)

lemma do_full1_cp_step_full:
  "full cdcl\<^sub>W_cp (rough_state_of S)
    (rough_state_of (do_full1_cp_step S))"
  unfolding full_def
proof (rule conjI, induction S rule: do_full1_cp_step.induct)
  case (1 S)
  then have f1:
      "cdcl\<^sub>W_cp\<^sup>*\<^sup>* ((do_cp_step (rough_state_of S))) (
         (rough_state_of (do_full1_cp_step (state_of (do_cp_step (rough_state_of S))))))
      \<or> state_of (do_cp_step (rough_state_of S)) = S"
    using rough_state_of_state_of_do_cp_step[of S] unfolding do_cp_step'_def by fastforce
  have f2: "\<And>c. (if c = state_of (do_cp_step (rough_state_of c))
       then c else do_full1_cp_step (state_of (do_cp_step (rough_state_of c))))
     = do_full1_cp_step c"
    by (metis (full_types) do_cp_step'_def do_full1_cp_step.simps)
  have f3: "\<not> cdcl\<^sub>W_cp  (rough_state_of S) (do_cp_step (rough_state_of S))
    \<or> state_of (do_cp_step (rough_state_of S)) = S
    \<or> cdcl\<^sub>W_cp\<^sup>+\<^sup>+ (rough_state_of S)
        (rough_state_of (do_full1_cp_step (state_of (do_cp_step (rough_state_of S)))))"
    using f1 by (meson rtranclp_into_tranclp2)
  { assume "do_full1_cp_step S \<noteq> S"
    then have "do_cp_step (rough_state_of S) = rough_state_of S
        \<longrightarrow> cdcl\<^sub>W_cp\<^sup>*\<^sup>* (rough_state_of S) (rough_state_of (do_full1_cp_step S))
      \<or> do_cp_step (rough_state_of S) \<noteq> rough_state_of S
        \<and> state_of (do_cp_step (rough_state_of S)) \<noteq> S"
      using f2 f1 by (metis (no_types))
    then have "do_cp_step (rough_state_of S) \<noteq> rough_state_of S
        \<and> state_of (do_cp_step (rough_state_of S)) \<noteq> S
      \<or> cdcl\<^sub>W_cp\<^sup>*\<^sup>* (rough_state_of S) (rough_state_of (do_full1_cp_step S))"
      by (metis rough_state_of_state_of_do_cp_step)
    then have "cdcl\<^sub>W_cp\<^sup>*\<^sup>* (rough_state_of S) (rough_state_of (do_full1_cp_step S))"
      using f3 f2 by (metis (no_types) cp_step_is_cdcl\<^sub>W_cp tranclp_into_rtranclp) }
  then show ?case
    by fastforce
next
  show "no_step cdcl\<^sub>W_cp (rough_state_of (do_full1_cp_step S))"
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
  assumes inv: "cdcl\<^sub>W_all_struct_inv S" and
  st: "do_other_step S \<noteq> S"
  shows "cdcl\<^sub>W_o S (do_other_step S)"
  using st inv by (auto split: if_split_asm
    simp add: Let_def
    intro: do_skip_step do_resolve_step do_backtrack_step do_decide_step
     cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros)

lemma do_other_step_no:
  assumes inv: "cdcl\<^sub>W_all_struct_inv S" and
  st: "do_other_step S = S"
  shows "no_step cdcl\<^sub>W_o S"
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
  have "cdcl\<^sub>W_o (rough_state_of S) (do_other_step (rough_state_of S))"
    by (metis False cdcl\<^sub>W_all_struct_inv_rough_state do_other_step["of" "rough_state_of S"])
  then have "cdcl\<^sub>W_all_struct_inv (do_other_step (rough_state_of S))"
    using cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_all_struct_inv_rough_state other by blast
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
 using do_other_step[of "rough_state_of S"] by (auto intro: cdcl\<^sub>W_all_struct_inv_inv
   cdcl\<^sub>W_all_struct_inv_rough_state other state_of_inverse)

definition do_cdcl\<^sub>W_stgy_step where
"do_cdcl\<^sub>W_stgy_step S =
   (let T = do_full1_cp_step S in
     if T \<noteq> S
     then T
     else
       (let U = (do_other_step' T) in
        (do_full1_cp_step U))) "

definition do_cdcl\<^sub>W_stgy_step' where
"do_cdcl\<^sub>W_stgy_step' S = state_from_init_state_of (rough_state_of (do_cdcl\<^sub>W_stgy_step (id_of_I_to S)))"

lemma toS_do_full1_cp_step_not_eq: "do_full1_cp_step S \<noteq> S \<Longrightarrow>
    rough_state_of S \<noteq> rough_state_of (do_full1_cp_step S)"
proof -
  assume a1: "do_full1_cp_step S \<noteq> S"
  then have "S \<noteq> do_cp_step' S"
    by fastforce
  then show ?thesis
    by (metis (no_types) do_cp_step'_def  do_full1_cp_step_fix_point_of_do_full1_cp_step
      rough_state_of_inverse)
qed

text \<open>@{term do_full1_cp_step} should not be unfolded anymore:\<close>
declare do_full1_cp_step.simps[simp del]

paragraph \<open>Correction of the transformation\<close>
lemma do_cdcl\<^sub>W_stgy_step:
  assumes "do_cdcl\<^sub>W_stgy_step S \<noteq> S"
  shows "cdcl\<^sub>W_stgy (rough_state_of S) (rough_state_of (do_cdcl\<^sub>W_stgy_step S))"
proof (cases "do_full1_cp_step S = S")
  case False
  then show ?thesis
    using assms do_full1_cp_step_full[of S] unfolding full_unfold do_cdcl\<^sub>W_stgy_step_def
    by (auto intro!: cdcl\<^sub>W_stgy.intros dest: toS_do_full1_cp_step_not_eq)
next
  case True
  have "cdcl\<^sub>W_o (rough_state_of S) (rough_state_of (do_other_step' S))"
    by (smt True assms cdcl\<^sub>W_all_struct_inv_rough_state do_cdcl\<^sub>W_stgy_step_def do_other_step
      rough_state_of_do_other_step' rough_state_of_inverse)
  moreover
    have
      np: "no_step propagate (rough_state_of S)" and
      nc: "no_step conflict (rough_state_of S)"
        apply (metis True cdcl\<^sub>W_cp.simps do_cp_step_eq_no_step
          do_full1_cp_step_fix_point_of_do_full1_cp_step in_clauses_rough_state_of_is_distinct)
      by (metis True do_conflict_step_no_step do_cp_step_eq_no_prop_no_confl
        do_full1_cp_step_fix_point_of_do_full1_cp_step)
    then have "no_step cdcl\<^sub>W_cp (rough_state_of S)"
      by (simp add: cdcl\<^sub>W_cp.simps)
  moreover have "full cdcl\<^sub>W_cp (rough_state_of (do_other_step' S))
    (rough_state_of (do_full1_cp_step (do_other_step' S)))"
    using do_full1_cp_step_full by auto
  ultimately show ?thesis
    using assms True unfolding do_cdcl\<^sub>W_stgy_step_def
    by (auto intro!: cdcl\<^sub>W_stgy.other' dest: toS_do_full1_cp_step_not_eq)
qed

lemma do_skip_step_trail_changed_or_conflict:
  assumes d: "do_other_step S \<noteq> S"
  and inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "trail S \<noteq> trail (do_other_step S)"
proof -
  have M: "\<And>M K M1 c. M = c @ K # M1 \<Longrightarrow> Suc (length M1) \<le> length M"
    by auto
  have "cdcl\<^sub>W_M_level_inv S"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have "cdcl\<^sub>W_o S (do_other_step S)" using do_other_step[OF inv d] .
  then show ?thesis
    using \<open>cdcl\<^sub>W_M_level_inv S\<close>
    proof (induction "do_other_step S" rule: cdcl\<^sub>W_o_induct_lev2)
      case decide
      then show ?thesis
        apply (cases S) (* TODO Tune proof *)
        apply (auto dest!: find_first_unused_var_Some
          simp: split: option.splits)
        by (meson atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set contra_subsetD)
    next
    case (skip)
    then show ?case
      by (cases S; cases "do_other_step S") force
    next
      case (resolve)
      then show ?case
         by (cases S, cases "do_other_step S") force
    next
      case (backtrack K i M1 M2 L D) note decomp = this(1) and confl_S = this(3) and undef = this(6)
        and U = this(7)
      then show ?case
        apply (cases "do_other_step S")
        apply (auto split: if_split_asm simp: Let_def)
            apply (cases S rule: do_skip_step.cases; auto split: if_split_asm)
           apply (cases S rule: do_skip_step.cases; auto split: if_split_asm)

          apply (cases S rule: do_backtrack_step.cases;
            auto split: if_split_asm option.splits list.splits marked_lit.splits
              dest!: bt_cut_some_decomp simp: Let_def)
        using d apply (cases S rule: do_decide_step.cases; auto split: option.splits)[]
        done
    qed
qed

lemma do_full1_cp_step_induct:
  "(\<And>S. (S \<noteq>  do_cp_step' S \<Longrightarrow> P (do_cp_step' S)) \<Longrightarrow> P S) \<Longrightarrow> P a0"
  using do_full1_cp_step.induct by metis

lemma do_cp_step_neq_trail_increase:
  "\<exists>c. raw_trail (do_cp_step S) = c @ raw_trail S \<and>(\<forall>m \<in> set c. \<not> is_marked m)"
  by (cases S, cases "raw_conflicting S")
     (auto simp add: do_cp_step_def do_conflict_step_def do_propagate_step_def split: option.splits)

lemma do_full1_cp_step_neq_trail_increase:
  "\<exists>c. raw_trail (rough_state_of (do_full1_cp_step S)) = c @ raw_trail (rough_state_of S)
    \<and> (\<forall>m \<in> set c. \<not> is_marked m)"
  apply (induction rule: do_full1_cp_step_induct)
  apply (rename_tac S, case_tac "do_cp_step' S = S")
    apply (simp add: do_full1_cp_step.simps)
  by (smt Un_iff append_assoc do_cp_step'_def do_cp_step_neq_trail_increase do_full1_cp_step.simps
    rough_state_of_state_of_do_cp_step set_append)

lemma do_cp_step_conflicting:
  "conflicting (rough_state_of S) \<noteq> None \<Longrightarrow> do_cp_step' S = S"
  unfolding do_cp_step'_def do_cp_step_def by simp

lemma do_full1_cp_step_conflicting:
  "conflicting (rough_state_of S) \<noteq> None \<Longrightarrow> do_full1_cp_step S = S"
  unfolding do_cp_step'_def do_cp_step_def
  apply (induction rule: do_full1_cp_step_induct)
  by (rename_tac S, case_tac "S \<noteq> do_cp_step' S")
   (auto simp add: do_full1_cp_step.simps do_cp_step_conflicting)

lemma do_decide_step_not_conflicting_one_more_decide:
  assumes
    "conflicting S = None" and
    "do_decide_step S \<noteq> S"
  shows "Suc (length (filter is_marked (raw_trail S)))
    = length (filter is_marked (raw_trail (do_decide_step S)))"
  using assms unfolding do_other_step'_def
  by (cases S) (force simp: Let_def split: if_split_asm option.splits
     dest!: find_first_unused_var_Some_not_all_incl)

lemma do_decide_step_not_conflicting_one_more_decide_bt:
  assumes "conflicting S \<noteq> None" and
  "do_decide_step S \<noteq> S"
  shows "length (filter is_marked (raw_trail S)) <
    length (filter is_marked (raw_trail (do_decide_step S)))"
  using assms unfolding do_other_step'_def by (cases S, cases "conflicting S")
    (auto simp add: Let_def split: if_split_asm option.splits)

lemma do_other_step_not_conflicting_one_more_decide_bt:
  assumes
    "conflicting (rough_state_of S) \<noteq> None" and
    "conflicting (rough_state_of (do_other_step' S)) = None" and
    "do_other_step' S \<noteq> S"
  shows "length (filter is_marked (raw_trail (rough_state_of S)))
    > length (filter is_marked (raw_trail (rough_state_of (do_other_step' S))))"
proof (cases S, goal_cases)
  case (1 y) note S = this(1) and inv = this(2)
  obtain M N U k E where y: "y = (M, N, U, k, Some E)"
    using assms(1) S inv by (cases y, cases "conflicting y") auto
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
      have "
        (raw_trail (rough_state_of (do_other_step' S)),
        raw_init_clss (rough_state_of (do_other_step' S)),
          raw_learned_clss (rough_state_of (do_other_step' S)),
          raw_backtrack_lvl (rough_state_of (do_other_step' S)), None)
        = rough_state_of (do_other_step' S)"
        using assms(2) by (cases "do_other_step' S") auto
      then show ?thesis
        using f3 2 by (metis (no_types) do_decide_step.simps(2) do_resolve_step_trail_is_None
          do_skip_step_trail_is_None rough_state_of_inverse)
    qed
  show ?case
    using assms(2) S unfolding bt y inv
    apply simp
    by (auto simp add: M bt_cut_not_none
          split: option.splits
          dest!: bt_cut_some_decomp)
qed

lemma do_other_step_not_conflicting_one_more_decide:
  assumes "conflicting (rough_state_of S) = None" and
  "do_other_step' S \<noteq> S"
  shows "1 + length (filter is_marked (raw_trail (rough_state_of S)))
    = length (filter is_marked (raw_trail (rough_state_of (do_other_step' S))))"
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
    using f6 f5 f4 by (simp add: assms(1) do_decide_step_not_conflicting_one_more_decide
      do_other_step'_def)
qed

lemma rough_state_of_state_of_do_skip_step_rough_state_of[simp]:
  "rough_state_of (state_of (do_skip_step (rough_state_of S))) = do_skip_step (rough_state_of S)"
  by (smt do_other_step.simps rough_state_of_inverse rough_state_of_state_of_do_other_step)

lemma conflicting_do_resolve_step_iff[iff]:
  "conflicting (do_resolve_step S) = None \<longleftrightarrow> conflicting S = None"
  by (cases S rule: do_resolve_step.cases)
   (auto simp add: Let_def split: option.splits)

lemma conflicting_do_skip_step_iff[iff]:
  "conflicting (do_skip_step S) = None \<longleftrightarrow> conflicting S = None"
  by (cases S rule: do_skip_step.cases)
     (auto simp add: Let_def split: option.splits)

lemma conflicting_do_decide_step_iff[iff]:
  "conflicting (do_decide_step S) = None \<longleftrightarrow> conflicting S = None"
  by (cases S rule: do_decide_step.cases)
     (auto simp add: Let_def split: option.splits)

lemma conflicting_do_backtrack_step_imp[simp]:
  "do_backtrack_step S \<noteq> S \<Longrightarrow> conflicting (do_backtrack_step S) = None"
  by (cases S rule: do_backtrack_step.cases)
     (auto simp add: Let_def split: list.splits option.splits marked_lit.splits)

lemma do_skip_step_eq_iff_trail_eq:
  "do_skip_step S = S \<longleftrightarrow> trail (do_skip_step S) = trail S"
  by (cases S rule: do_skip_step.cases) auto

lemma do_decide_step_eq_iff_trail_eq:
  "do_decide_step S = S \<longleftrightarrow> trail (do_decide_step S) = trail S"
  by (cases S rule: do_decide_step.cases) (auto split: option.split)

lemma do_backtrack_step_eq_iff_trail_eq:
  "do_backtrack_step S = S \<longleftrightarrow> raw_trail (do_backtrack_step S) = raw_trail S"
  by (cases S rule: do_backtrack_step.cases)
     (auto split: option.split list.splits marked_lit.splits
       dest!: bt_cut_in_get_all_marked_decomposition)

lemma do_resolve_step_eq_iff_trail_eq:
  "do_resolve_step S = S \<longleftrightarrow> trail (do_resolve_step S) = trail S"
  by (cases S rule: do_resolve_step.cases) auto

lemma do_other_step_eq_iff_trail_eq:
  "do_other_step S = S \<longleftrightarrow> raw_trail (do_other_step S) = raw_trail S"
  (* TODO proof *)
  apply
  (auto simp add: Let_def do_skip_step_eq_iff_trail_eq
    do_decide_step_eq_iff_trail_eq do_backtrack_step_eq_iff_trail_eq
    do_resolve_step_eq_iff_trail_eq
    )
  apply (simp add: do_resolve_step_eq_iff_trail_eq[symmetric]
     do_skip_step_eq_iff_trail_eq[symmetric])
  apply (simp add: do_skip_step_eq_iff_trail_eq[symmetric]
    do_decide_step_eq_iff_trail_eq  do_backtrack_step_eq_iff_trail_eq[symmetric]
    do_resolve_step_eq_iff_trail_eq[symmetric]
    )
  done

lemma do_full1_cp_step_do_other_step'_normal_form[dest!]:
  assumes H: "do_full1_cp_step (do_other_step' S) = S"
  shows "do_other_step' S = S \<and> do_full1_cp_step S = S"
proof -
  let ?T = "do_other_step' S"
  { assume confl: "conflicting (rough_state_of ?T) \<noteq> None"
    then have tr: "trail (rough_state_of (do_full1_cp_step ?T)) = trail (rough_state_of ?T)"
      using do_full1_cp_step_conflicting by fastforce
    have "raw_trail (rough_state_of (do_full1_cp_step (do_other_step' S))) =
      raw_trail (rough_state_of S)"
      using arg_cong[OF H, of "\<lambda>S. raw_trail (rough_state_of S)"] .
    then have "raw_trail (rough_state_of (do_other_step' S)) = raw_trail (rough_state_of S)"
       using confl by (auto simp add: do_full1_cp_step_conflicting)
    then have "do_other_step' S = S"
      by (simp add: do_other_step_eq_iff_trail_eq[symmetric] do_other_step'_def
        del: do_other_step.simps)
  }
  moreover {
    assume eq[simp]: "do_other_step' S = S"
    obtain c where c: "raw_trail (rough_state_of (do_full1_cp_step S)) =
      c @ raw_trail (rough_state_of S)"
      using do_full1_cp_step_neq_trail_increase by auto

    moreover have "raw_trail (rough_state_of (do_full1_cp_step S)) = raw_trail (rough_state_of S)"
      using arg_cong[OF H, of "\<lambda>S. raw_trail (rough_state_of S)"] by simp
    finally have "c = []" by blast
    then have "do_full1_cp_step S = S" using assms by auto
    }
  moreover {
    assume confl: "conflicting (rough_state_of ?T) = None" and neq: "do_other_step' S \<noteq> S"
    obtain c where
      c: "raw_trail (rough_state_of (do_full1_cp_step ?T)) = c @ raw_trail (rough_state_of ?T)" and
      nm: "\<forall>m\<in>set c. \<not> is_marked m"
      using do_full1_cp_step_neq_trail_increase by auto
    have "length (filter is_marked (raw_trail (rough_state_of (do_full1_cp_step ?T))))
       = length (filter is_marked (raw_trail (rough_state_of ?T)))"
      using nm unfolding c by force
    moreover have "length (filter is_marked (raw_trail (rough_state_of S)))
       \<noteq> length (filter is_marked (raw_trail (rough_state_of ?T)))"
      using do_other_step_not_conflicting_one_more_decide[OF _ neq]
      do_other_step_not_conflicting_one_more_decide_bt[of S, OF _ confl neq]
      by linarith
    finally have False unfolding H by blast
  }
  ultimately show ?thesis by blast
qed

lemma do_cdcl\<^sub>W_stgy_step_no:
  assumes S: "do_cdcl\<^sub>W_stgy_step S = S"
  shows "no_step cdcl\<^sub>W_stgy (rough_state_of S)"
proof -
  {
    fix S'
    assume "full1 cdcl\<^sub>W_cp (rough_state_of S) S'"
    then have False
      using do_full1_cp_step_full[of S] unfolding full_def S rtranclp_unfold full1_def
      by (smt assms do_cdcl\<^sub>W_stgy_step_def tranclpD)
  }
  moreover {
    fix S' S''
    assume " cdcl\<^sub>W_o (rough_state_of S) S'" and
     "no_step propagate (rough_state_of S)" and
     "no_step conflict (rough_state_of S)" and
     "full cdcl\<^sub>W_cp S' S''"
    then have False
      using assms unfolding do_cdcl\<^sub>W_stgy_step_def
      by (smt cdcl\<^sub>W_all_struct_inv_rough_state do_full1_cp_step_do_other_step'_normal_form
        do_other_step_no rough_state_of_do_other_step')
  }
  ultimately show ?thesis using assms by (force simp: cdcl\<^sub>W_cp.simps cdcl\<^sub>W_stgy.simps)
qed

lemma toS_rough_state_of_state_of_rough_state_from_init_state_of[simp]:
  "rough_state_of (state_of (rough_state_from_init_state_of S))
    = rough_state_from_init_state_of S"
  using rough_state_from_init_state_of[of S] by (auto simp add: state_of_inverse)

lemma cdcl\<^sub>W_cp_is_rtranclp_cdcl\<^sub>W: "cdcl\<^sub>W_cp S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  apply (induction rule: cdcl\<^sub>W_cp.induct)
   using conflict apply blast
  using propagate by blast

lemma rtranclp_cdcl\<^sub>W_cp_is_rtranclp_cdcl\<^sub>W: "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  apply (induction rule: rtranclp_induct)
    apply simp
  by (fastforce dest!: cdcl\<^sub>W_cp_is_rtranclp_cdcl\<^sub>W)

lemma cdcl\<^sub>W_stgy_is_rtranclp_cdcl\<^sub>W:
  "cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  apply (induction rule: cdcl\<^sub>W_stgy.induct)
   using cdcl\<^sub>W_stgy.conflict' rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W apply blast
  unfolding full_def by (fastforce dest!:other rtranclp_cdcl\<^sub>W_cp_is_rtranclp_cdcl\<^sub>W)

lemma cdcl\<^sub>W_stgy_init_clss: "cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_M_level_inv S \<Longrightarrow> init_clss S = init_clss T"
  using rtranclp_cdcl\<^sub>W_init_clss cdcl\<^sub>W_stgy_is_rtranclp_cdcl\<^sub>W by fast

lemma clauses_toS_rough_state_of_do_cdcl\<^sub>W_stgy_step[simp]:
  "init_clss (rough_state_of (do_cdcl\<^sub>W_stgy_step (state_of (rough_state_from_init_state_of S))))
    = init_clss (rough_state_from_init_state_of S)" (is "_ = init_clss ?S")
proof (cases "do_cdcl\<^sub>W_stgy_step (state_of ?S) = state_of ?S")
  case True
  then show ?thesis by simp
next
  case False
  have "\<And>c. cdcl\<^sub>W_M_level_inv (rough_state_of c)"
    using cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_all_struct_inv_rough_state by blast
  then have "\<And>c. init_clss (rough_state_of c) = init_clss (rough_state_of (do_cdcl\<^sub>W_stgy_step c))
    \<or> do_cdcl\<^sub>W_stgy_step c = c"
    using cdcl\<^sub>W_stgy_no_more_init_clss do_cdcl\<^sub>W_stgy_step by blast
  then show ?thesis
    using False by force
qed

lemma raw_init_clss_do_cp_step[simp]:
  "raw_init_clss (do_cp_step S) = raw_init_clss S"
 by (cases S) (auto simp: do_cp_step_def do_propagate_step_def do_conflict_step_def
  split: option.splits)
lemma raw_init_clss_do_cp_step'[simp]:
  "raw_init_clss (rough_state_of (do_cp_step' S)) = raw_init_clss (rough_state_of S)"
  by (simp add: do_cp_step'_def)

lemma raw_init_clss_rough_state_of_do_full1_cp_step[simp]:
  "raw_init_clss (rough_state_of (do_full1_cp_step S))
 = raw_init_clss (rough_state_of S)"
  apply (rule do_full1_cp_step.induct[of "\<lambda>S.
    raw_init_clss (rough_state_of (do_full1_cp_step S))
 = raw_init_clss (rough_state_of S)"])
  by (metis (mono_tags, lifting) do_full1_cp_step.simps raw_init_clss_do_cp_step')

lemma raw_init_clss_do_skip_def[simp]:
  "raw_init_clss (do_skip_step S) = raw_init_clss S"
  by (cases S rule: do_skip_step.cases) (auto simp: do_other_step'_def Let_def
  split: option.splits)

lemma raw_init_clss_do_resolve_def[simp]:
  "raw_init_clss (do_resolve_step S) = raw_init_clss S"
  by (cases S rule: do_resolve_step.cases) (auto simp: do_other_step'_def Let_def
  split: option.splits)

lemma raw_init_clss_do_backtrack_def[simp]:
  "raw_init_clss (do_backtrack_step S) = raw_init_clss S"
  by (cases S rule: do_backtrack_step.cases) (auto simp: do_other_step'_def Let_def
  split: option.splits list.splits marked_lit.splits)


lemma raw_init_clss_do_decide_def[simp]:
  "raw_init_clss (do_decide_step S) = raw_init_clss S"
  by (cases S rule: do_decide_step.cases) (auto simp: do_other_step'_def Let_def
   split: option.splits)

lemma raw_init_clss_rough_state_of_do_other_step'[simp]:
  "raw_init_clss (rough_state_of (do_other_step' S))
  = raw_init_clss (rough_state_of S)"
  by (cases S) (auto simp: do_other_step'_def Let_def do_skip_step.cases
  split: option.splits)

lemma [simp]:
  "raw_init_clss (rough_state_of (do_cdcl\<^sub>W_stgy_step (state_of (rough_state_from_init_state_of S))))
  =
  raw_init_clss (rough_state_from_init_state_of S)"
  unfolding do_cdcl\<^sub>W_stgy_step_def by (auto simp: Let_def)

lemma rough_state_from_init_state_of_do_cdcl\<^sub>W_stgy_step'[code abstract]:
 "rough_state_from_init_state_of (do_cdcl\<^sub>W_stgy_step' S) =
   rough_state_of (do_cdcl\<^sub>W_stgy_step (id_of_I_to S))"
proof -
  let ?S = "(rough_state_from_init_state_of S)"
  have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (raw_S0_cdcl\<^sub>W (raw_init_clss (rough_state_from_init_state_of S)))
    (rough_state_from_init_state_of S)"
    using rough_state_from_init_state_of[of S] by auto
  moreover have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>*
                  (rough_state_from_init_state_of S)
                  (rough_state_of (do_cdcl\<^sub>W_stgy_step
                    (state_of (rough_state_from_init_state_of S))))"
     using do_cdcl\<^sub>W_stgy_step[of "state_of ?S"]
     by (cases "do_cdcl\<^sub>W_stgy_step (state_of ?S) = state_of ?S") auto
  ultimately show ?thesis
    unfolding do_cdcl\<^sub>W_stgy_step'_def id_of_I_to_def
    by (auto intro: state_from_init_state_of_inverse)
qed

paragraph \<open>All rules together\<close>
function do_all_cdcl\<^sub>W_stgy where
"do_all_cdcl\<^sub>W_stgy S =
  (let T = do_cdcl\<^sub>W_stgy_step' S in
  if T = S then S else do_all_cdcl\<^sub>W_stgy T)"
by fast+
termination
proof (relation "{(T, S).
    (cdcl\<^sub>W_measure (rough_state_from_init_state_of T),
    cdcl\<^sub>W_measure (rough_state_from_init_state_of S))
      \<in> lexn less_than 3}", goal_cases)
  case 1
  show ?case by (rule wf_if_measure_f) (auto intro!: wf_lexn wf_less)
next
  case (2 S T) note T = this(1) and ST = this(2)
  let ?S = "rough_state_from_init_state_of S"
  have S: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (raw_S0_cdcl\<^sub>W (raw_init_clss ?S)) ?S"
    using rough_state_from_init_state_of[of S] by auto
  moreover have "cdcl\<^sub>W_stgy (rough_state_from_init_state_of S)
    (rough_state_from_init_state_of T)"

    proof -
      have "\<And>c. rough_state_of (state_of (rough_state_from_init_state_of c)) =
        rough_state_from_init_state_of c"
        using rough_state_from_init_state_of by force
      then have "do_cdcl\<^sub>W_stgy_step (state_of (rough_state_from_init_state_of S))
        \<noteq> state_of (rough_state_from_init_state_of S)"
        using ST T  rough_state_from_init_state_of_inverse
        unfolding id_of_I_to_def do_cdcl\<^sub>W_stgy_step'_def
        by fastforce
      from do_cdcl\<^sub>W_stgy_step[OF this] show ?thesis
        by (simp add: T id_of_I_to_def rough_state_from_init_state_of_do_cdcl\<^sub>W_stgy_step')
    qed
  moreover
    have "cdcl\<^sub>W_all_struct_inv (rough_state_from_init_state_of S)"
      using rough_state_from_init_state_of[of S] by auto
    then have "cdcl\<^sub>W_all_struct_inv (raw_S0_cdcl\<^sub>W (raw_init_clss (rough_state_from_init_state_of S)))"
      by (cases "rough_state_from_init_state_of S")
         (auto simp add: cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def)
  ultimately show ?case
    by (auto intro!: cdcl\<^sub>W_stgy_step_decreasing[of _ _ "raw_S0_cdcl\<^sub>W (raw_init_clss ?S)"]
      simp del: cdcl\<^sub>W_measure.simps)
qed

thm do_all_cdcl\<^sub>W_stgy.induct
lemma do_all_cdcl\<^sub>W_stgy_induct:
  "(\<And>S. (do_cdcl\<^sub>W_stgy_step' S \<noteq> S \<Longrightarrow> P (do_cdcl\<^sub>W_stgy_step' S)) \<Longrightarrow> P S) \<Longrightarrow> P a0"
 using do_all_cdcl\<^sub>W_stgy.induct by metis

lemma [simp]: "raw_init_clss (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy S)) =
  raw_init_clss (rough_state_from_init_state_of S)"
  apply (induction rule: do_all_cdcl\<^sub>W_stgy_induct)
  by (smt do_all_cdcl\<^sub>W_stgy.simps do_cdcl\<^sub>W_stgy_step_def id_of_I_to_def
    raw_init_clss_rough_state_of_do_full1_cp_step raw_init_clss_rough_state_of_do_other_step'
    rough_state_from_init_state_of_do_cdcl\<^sub>W_stgy_step'
    toS_rough_state_of_state_of_rough_state_from_init_state_of)

lemma no_step_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all:
  fixes S :: "'a cdcl\<^sub>W_state_inv_from_init_state"
  shows "no_step cdcl\<^sub>W_stgy (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy S))"
  apply (induction S rule:do_all_cdcl\<^sub>W_stgy_induct)
  apply (rename_tac S, case_tac "do_cdcl\<^sub>W_stgy_step' S \<noteq> S")
proof -
  fix Sa :: "'a cdcl\<^sub>W_state_inv_from_init_state"
  assume a1: "\<not> do_cdcl\<^sub>W_stgy_step' Sa \<noteq> Sa"
  { fix pp
    have "(if True then Sa else do_all_cdcl\<^sub>W_stgy Sa) = do_all_cdcl\<^sub>W_stgy Sa"
      using a1 by auto
    then have "\<not> cdcl\<^sub>W_stgy (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy Sa)) pp"
      using a1 by (smt do_cdcl\<^sub>W_stgy_step_no id_of_I_to_def
        rough_state_from_init_state_of_do_cdcl\<^sub>W_stgy_step' rough_state_of_inverse) }
  then show "no_step cdcl\<^sub>W_stgy (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy Sa))"
    by fastforce
next
  fix Sa :: "'a cdcl\<^sub>W_state_inv_from_init_state"
  assume a1: "do_cdcl\<^sub>W_stgy_step' Sa \<noteq> Sa
    \<Longrightarrow> no_step cdcl\<^sub>W_stgy (rough_state_from_init_state_of
      (do_all_cdcl\<^sub>W_stgy (do_cdcl\<^sub>W_stgy_step' Sa)))"
  assume a2: "do_cdcl\<^sub>W_stgy_step' Sa \<noteq> Sa"
  have "do_all_cdcl\<^sub>W_stgy Sa = do_all_cdcl\<^sub>W_stgy (do_cdcl\<^sub>W_stgy_step' Sa)"
    by (metis (full_types) do_all_cdcl\<^sub>W_stgy.simps)
  then show "no_step cdcl\<^sub>W_stgy (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy Sa))"
    using a2 a1 by presburger
qed

lemma do_all_cdcl\<^sub>W_stgy_is_rtranclp_cdcl\<^sub>W_stgy:
  "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (rough_state_from_init_state_of S)
    (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy S))"
proof (induction S rule: do_all_cdcl\<^sub>W_stgy_induct)
  case (1 S) note IH = this(1)
  show ?case
    proof (cases "do_cdcl\<^sub>W_stgy_step' S = S")
      case True
      then show ?thesis by simp
    next
      case False
      have f2: "do_cdcl\<^sub>W_stgy_step (id_of_I_to S) = id_of_I_to S \<longrightarrow>
        rough_state_from_init_state_of (do_cdcl\<^sub>W_stgy_step' S)
        = rough_state_of (state_of (rough_state_from_init_state_of S))"
        unfolding  rough_state_from_init_state_of_do_cdcl\<^sub>W_stgy_step'
        id_of_I_to_def by presburger
      have f3: "do_all_cdcl\<^sub>W_stgy S = do_all_cdcl\<^sub>W_stgy (do_cdcl\<^sub>W_stgy_step' S)"
        by (metis (full_types) do_all_cdcl\<^sub>W_stgy.simps)
      have "cdcl\<^sub>W_stgy (rough_state_from_init_state_of S)
          (rough_state_from_init_state_of (do_cdcl\<^sub>W_stgy_step' S))
        = cdcl\<^sub>W_stgy (rough_state_of (id_of_I_to S))
          (rough_state_of (do_cdcl\<^sub>W_stgy_step (id_of_I_to S)))"
        unfolding id_of_I_to_def rough_state_from_init_state_of_do_cdcl\<^sub>W_stgy_step'
        toS_rough_state_of_state_of_rough_state_from_init_state_of by presburger
      then show ?thesis
        using f3 f2 IH do_cdcl\<^sub>W_stgy_step
        by (smt False toS_rough_state_of_state_of_rough_state_from_init_state_of tranclp.intros(1)
          tranclp_into_rtranclp transitive_closurep_trans'(2))
    qed
qed

text \<open>Final theorem:\<close>
lemma consistent_interp_mmset_of_mlit[simp]:
  "consistent_interp (lit_of ` mmset_of_mlit' ` set M') \<longleftrightarrow>
   consistent_interp (lit_of ` set M')"
  by (auto simp: image_image)

lemma DPLL_tot_correct:
  assumes
    r: "rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy (state_from_init_state_of
      (([], map remdups N, [], 0, None)))) = S" and
    S: "(M', N', U', k, E) = S"
  shows "(E \<noteq> Some [] \<and> satisfiable (set (map mset N)))
    \<or> (E = Some [] \<and> unsatisfiable (set (map mset N)))"
proof -
  let ?N = "map remdups N"
  have inv: "cdcl\<^sub>W_all_struct_inv ([], map remdups N, [], 0, None)"
    unfolding cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def distinct_mset_set_def by auto
  then have S0: "rough_state_of (state_of ([], map remdups N, [], 0, None))
    = ([], map remdups N, [], 0, None)" by simp
  have 1: "full cdcl\<^sub>W_stgy ([], ?N, [], 0, None) S"
    unfolding full_def apply rule
      using do_all_cdcl\<^sub>W_stgy_is_rtranclp_cdcl\<^sub>W_stgy[of
        "state_from_init_state_of ([], map remdups N, [], 0, None)"] inv
        by (auto simp del: do_all_cdcl\<^sub>W_stgy.simps simp: state_from_init_state_of_inverse
          r[symmetric] no_step_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all)+
  moreover have 2: "finite (set (map mset ?N))" by auto
  moreover have 3: "distinct_mset_set (set (map mset ?N))"
     unfolding distinct_mset_set_def by auto
  moreover
    have "cdcl\<^sub>W_all_struct_inv S"
      by (metis (no_types) cdcl\<^sub>W_all_struct_inv_rough_state r
        toS_rough_state_of_state_of_rough_state_from_init_state_of)
    then have cons: "consistent_interp (lits_of_l M')"
      unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def S[symmetric]
      by (auto simp: lits_of_def)
  moreover
    have [simp]:
      "rough_state_from_init_state_of (state_from_init_state_of (raw_S0_cdcl\<^sub>W (map remdups N)))
      = raw_S0_cdcl\<^sub>W (map remdups N)"
      apply (rule cdcl\<^sub>W_state_inv_from_init_state.state_from_init_state_of_inverse)
      using 3 by (auto simp: cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def
        image_image comp_def)
    have "raw_init_clss ([], ?N, [], 0, None) = raw_init_clss S"
      using arg_cong[OF r, of raw_init_clss] unfolding S[symmetric]
      by (simp del: do_all_cdcl\<^sub>W_stgy.simps)
    then have N': "N' =map remdups N"
      using S[symmetric] by auto

  have "conflicting S = Some {#} \<and> unsatisfiable (set_mset (init_clss S)) \<or>
    conflicting S = None \<and> (case S of (M, uu_) \<Rightarrow> map mmset_of_mlit' M) \<Turnstile>asm init_clss S"
    apply (rule full_cdcl\<^sub>W_stgy_final_state_conclusive)
        using 1 apply simp
       using 2 apply simp
      using 3 by simp
  then have "(E \<noteq> Some [] \<and> satisfiable (set (map mset ?N)))
    \<or> (E = Some [] \<and> unsatisfiable (set (map mset ?N)))"
    using cons unfolding S[symmetric] N' apply (auto simp: comp_def)
    by (simp add: true_annots_true_cls)
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

export_code do_all_cdcl\<^sub>W_stgy gene in SML
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
  val max : 'a ord -> 'a -> 'a -> 'a
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

end; (*struct Orderings*)

structure Arith : sig
  datatype nat = Zero_nat | Suc of nat
  val equal_nata : nat -> nat -> bool
  val equal_nat : nat HOL.equal
  val less_nat : nat -> nat -> bool
  val ord_nat : nat Orderings.ord
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
  val lits_of :
    ('a, 'b, 'c) marked_lit Set.set -> 'a Clausal_Logic.literal Set.set
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

fun lits_of ls = Set.image lit_of ls;

end; (*struct Partial_Annotated_Clausal_Logic*)

structure CDCL_W_Level : sig
  val get_rev_level :
    'a HOL.equal ->
      ('a, Arith.nat, 'b) Partial_Annotated_Clausal_Logic.marked_lit list ->
        Arith.nat -> 'a Clausal_Logic.literal -> Arith.nat
end = struct

fun get_rev_level A_ [] uu uv = Arith.Zero_nat
  | get_rev_level A_ (Partial_Annotated_Clausal_Logic.Marked (la, level) :: ls)
    n l =
    (if HOL.eq A_ (Clausal_Logic.atm_of la) (Clausal_Logic.atm_of l) then level
      else get_rev_level A_ ls level l)
  | get_rev_level A_ (Partial_Annotated_Clausal_Logic.Propagated (la, uw) :: ls)
    n l =
    (if HOL.eq A_ (Clausal_Logic.atm_of la) (Clausal_Logic.atm_of l) then n
      else get_rev_level A_ ls n l);

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
        ('a, 'b, 'c) Partial_Annotated_Clausal_Logic.marked_lit list ->
          ('a Clausal_Logic.literal * 'a Clausal_Logic.literal list) option
end = struct

fun is_unit_clause_code A_ l m =
  (case List.filter
          (fn a =>
            not (Set.member A_ (Clausal_Logic.atm_of a)
                  (Set.image Clausal_Logic.atm_of
                    (Partial_Annotated_Clausal_Logic.lits_of (Set.Set m)))))
          l
    of [] => NONE
    | [a] =>
      (if List.list_all
            (fn c =>
              Set.member (Clausal_Logic.equal_literal A_)
                (Clausal_Logic.uminus_literal c)
                (Partial_Annotated_Clausal_Logic.lits_of (Set.Set m)))
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
  datatype 'a cdcl_W_state_inv_from_init_state =
    ConI of
      (('a, Arith.nat, ('a Clausal_Logic.literal list))
         Partial_Annotated_Clausal_Logic.marked_lit list *
        (('a Clausal_Logic.literal list) list *
          (('a Clausal_Logic.literal list) list *
            (Arith.nat * ('a Clausal_Logic.literal list) option))))
  val gene : Arith.nat -> (Arith.nat Clausal_Logic.literal list) list
  val do_all_cdcl_W_stgy :
    'a HOL.equal ->
      'a cdcl_W_state_inv_from_init_state -> 'a cdcl_W_state_inv_from_init_state
end = struct

datatype 'a cdcl_W_state_inv =
  Con of
    (('a, Arith.nat, ('a Clausal_Logic.literal list))
       Partial_Annotated_Clausal_Logic.marked_lit list *
      (('a Clausal_Logic.literal list) list *
        (('a Clausal_Logic.literal list) list *
          (Arith.nat * ('a Clausal_Logic.literal list) option))));

datatype 'a cdcl_W_state_inv_from_init_state =
  ConI of
    (('a, Arith.nat, ('a Clausal_Logic.literal list))
       Partial_Annotated_Clausal_Logic.marked_lit list *
      (('a Clausal_Logic.literal list) list *
        (('a Clausal_Logic.literal list) list *
          (Arith.nat * ('a Clausal_Logic.literal list) option))));

fun gene Arith.Zero_nat =
  [[Clausal_Logic.Pos Arith.Zero_nat], [Clausal_Logic.Neg Arith.Zero_nat]]
  | gene (Arith.Suc n) =
    List.map (fn a => Clausal_Logic.Pos (Arith.Suc n) :: a) (gene n) @
      List.map (fn a => Clausal_Logic.Neg (Arith.Suc n) :: a) (gene n);

fun bt_cut i (Partial_Annotated_Clausal_Logic.Propagated (uu, uv) :: ls) =
  bt_cut i ls
  | bt_cut i (Partial_Annotated_Clausal_Logic.Marked (ka, k) :: ls) =
    (if Arith.equal_nata k (Arith.Suc i)
      then SOME (Partial_Annotated_Clausal_Logic.Marked (ka, k) :: ls)
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
              (Partial_Annotated_Clausal_Logic.lits_of (Set.Set m)))
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

fun do_cp_stepa A_ s = Con (do_cp_step A_ (rough_state_of s));

fun do_skip_step A_
  (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls,
    (n, (u, (k, SOME d))))
  = (if not (List.member (Clausal_Logic.equal_literal A_) d
              (Clausal_Logic.uminus_literal l)) andalso
          not (List.null d)
      then (ls, (n, (u, (k, SOME d))))
      else (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls,
             (n, (u, (k, SOME d)))))
  | do_skip_step A_ ([], va) = ([], va)
  | do_skip_step A_ (Partial_Annotated_Clausal_Logic.Marked (vd, ve) :: vc, va)
    = (Partial_Annotated_Clausal_Logic.Marked (vd, ve) :: vc, va)
  | do_skip_step A_ (v, (vb, (vd, (vf, NONE)))) = (v, (vb, (vd, (vf, NONE))));

fun maximum_level_code A_ [] uu = Arith.Zero_nat
  | maximum_level_code A_ (l :: ls) m =
    Orderings.max Arith.ord_nat
      (CDCL_W_Level.get_rev_level A_ (List.rev m) Arith.Zero_nat l)
      (maximum_level_code A_ ls m);

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
        | SOME (Partial_Annotated_Clausal_Logic.Marked (_, _) :: ls) =>
          (Partial_Annotated_Clausal_Logic.Propagated (l, d) :: ls,
            (n, (d :: u, (j, NONE))))
        | SOME (Partial_Annotated_Clausal_Logic.Propagated (_, _) :: _) =>
          (m, (n, (u, (k, SOME d))))))
  | do_backtrack_step A_ (v, (vb, (vd, (vf, NONE)))) =
    (v, (vb, (vd, (vf, NONE))));

fun do_resolve_step A_
  (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls,
    (n, (u, (k, SOME d))))
  = (if List.member (Clausal_Logic.equal_literal A_) d
          (Clausal_Logic.uminus_literal l) andalso
          Arith.equal_nata
            (maximum_level_code A_
              (List.remove1 (Clausal_Logic.equal_literal A_)
                (Clausal_Logic.uminus_literal l) d)
              (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls))
            k
      then (ls, (n, (u, (k, SOME (List.remdups (Clausal_Logic.equal_literal A_)
                                   (List.remove1
                                      (Clausal_Logic.equal_literal A_) l c @
                                     List.remove1
                                       (Clausal_Logic.equal_literal A_)
                                       (Clausal_Logic.uminus_literal l) d))))))
      else (Partial_Annotated_Clausal_Logic.Propagated (l, c) :: ls,
             (n, (u, (k, SOME d)))))
  | do_resolve_step A_ ([], va) = ([], va)
  | do_resolve_step A_
    (Partial_Annotated_Clausal_Logic.Marked (vd, ve) :: vc, va) =
    (Partial_Annotated_Clausal_Logic.Marked (vd, ve) :: vc, va)
  | do_resolve_step A_ (v, (vb, (vd, (vf, NONE)))) =
    (v, (vb, (vd, (vf, NONE))));

fun do_decide_step A_ (m, (n, (u, (k, NONE)))) =
  (case DPLL_CDCL_W_Implementation.find_first_unused_var A_ n
          (Partial_Annotated_Clausal_Logic.lits_of (Set.Set m))
    of NONE => (m, (n, (u, (k, NONE))))
    | SOME l =>
      (Partial_Annotated_Clausal_Logic.Marked (l, Arith.Suc k) :: m,
        (n, (u, (Arith.plus_nat k Arith.one_nat, NONE)))))
  | do_decide_step A_ (v, (vb, (vd, (vf, SOME vh)))) =
    (v, (vb, (vd, (vf, SOME vh))));

fun do_other_step A_ s =
  let
    val t = do_skip_step A_ s;
  in
    (if not (Product_Type.equal_proda
              (List.equal_list
                (Partial_Annotated_Clausal_Logic.equal_marked_lit A_
                  Arith.equal_nat
                  (List.equal_list (Clausal_Logic.equal_literal A_))))
              (Product_Type.equal_prod
                (List.equal_list
                  (List.equal_list (Clausal_Logic.equal_literal A_)))
                (Product_Type.equal_prod
                  (List.equal_list
                    (List.equal_list (Clausal_Logic.equal_literal A_)))
                  (Product_Type.equal_prod Arith.equal_nat
                    (Option.equal_option
                      (List.equal_list (Clausal_Logic.equal_literal A_))))))
              t s)
      then t
      else let
             val u = do_resolve_step A_ t;
           in
             (if not (Product_Type.equal_proda
                       (List.equal_list
                         (Partial_Annotated_Clausal_Logic.equal_marked_lit A_
                           Arith.equal_nat
                           (List.equal_list (Clausal_Logic.equal_literal A_))))
                       (Product_Type.equal_prod
                         (List.equal_list
                           (List.equal_list (Clausal_Logic.equal_literal A_)))
                         (Product_Type.equal_prod
                           (List.equal_list
                             (List.equal_list (Clausal_Logic.equal_literal A_)))
                           (Product_Type.equal_prod Arith.equal_nat
                             (Option.equal_option
                               (List.equal_list
                                 (Clausal_Logic.equal_literal A_))))))
                       u t)
               then u
               else let
                      val v = do_backtrack_step A_ u;
                    in
                      (if not (Product_Type.equal_proda
                                (List.equal_list
                                  (Partial_Annotated_Clausal_Logic.equal_marked_lit
                                    A_ Arith.equal_nat
                                    (List.equal_list
                                      (Clausal_Logic.equal_literal A_))))
                                (Product_Type.equal_prod
                                  (List.equal_list
                                    (List.equal_list
                                      (Clausal_Logic.equal_literal A_)))
                                  (Product_Type.equal_prod
                                    (List.equal_list
                                      (List.equal_list
(Clausal_Logic.equal_literal A_)))
                                    (Product_Type.equal_prod Arith.equal_nat
                                      (Option.equal_option
(List.equal_list (Clausal_Logic.equal_literal A_))))))
                                v u)
                        then v else do_decide_step A_ v)
                    end)
           end)
  end;

fun do_other_stepa A_ s = Con (do_other_step A_ (rough_state_of s));

fun equal_cdcl_W_state_inv A_ sa s =
  Product_Type.equal_proda
    (List.equal_list
      (Partial_Annotated_Clausal_Logic.equal_marked_lit A_ Arith.equal_nat
        (List.equal_list (Clausal_Logic.equal_literal A_))))
    (Product_Type.equal_prod
      (List.equal_list (List.equal_list (Clausal_Logic.equal_literal A_)))
      (Product_Type.equal_prod
        (List.equal_list (List.equal_list (Clausal_Logic.equal_literal A_)))
        (Product_Type.equal_prod Arith.equal_nat
          (Option.equal_option
            (List.equal_list (Clausal_Logic.equal_literal A_))))))
    (rough_state_of sa) (rough_state_of s);

fun do_full1_cp_step A_ s =
  let
    val sa = do_cp_stepa A_ s;
  in
    (if equal_cdcl_W_state_inv A_ s sa then s else do_full1_cp_step A_ sa)
  end;

fun equal_cdcl_W_state_inv_from_init_state A_ sa s =
  Product_Type.equal_proda
    (List.equal_list
      (Partial_Annotated_Clausal_Logic.equal_marked_lit A_ Arith.equal_nat
        (List.equal_list (Clausal_Logic.equal_literal A_))))
    (Product_Type.equal_prod
      (List.equal_list (List.equal_list (Clausal_Logic.equal_literal A_)))
      (Product_Type.equal_prod
        (List.equal_list (List.equal_list (Clausal_Logic.equal_literal A_)))
        (Product_Type.equal_prod Arith.equal_nat
          (Option.equal_option
            (List.equal_list (Clausal_Logic.equal_literal A_))))))
    (rough_state_from_init_state_of sa) (rough_state_from_init_state_of s);

fun do_cdcl_W_stgy_step A_ s =
  let
    val t = do_full1_cp_step A_ s;
  in
    (if not (equal_cdcl_W_state_inv A_ t s) then t
      else let
             val a = do_other_stepa A_ t;
           in
             do_full1_cp_step A_ a
           end)
  end;

fun do_cdcl_W_stgy_stepa A_ s =
  ConI (rough_state_of (do_cdcl_W_stgy_step A_ (id_of_I_to s)));

fun do_all_cdcl_W_stgy A_ s =
  let
    val t = do_cdcl_W_stgy_stepa A_ s;
  in
    (if equal_cdcl_W_state_inv_from_init_state A_ t s then s
      else do_all_cdcl_W_stgy A_ t)
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
  val f = do_all_cdcl_W_stgy equal_nat
    (CDCL_W_Implementation.ConI ([], (N, ([], (Zero_nat, NONE)))))
  in
  f
end
\<close>
(*>*)

end
