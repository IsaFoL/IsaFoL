theory CDCL_W_Implementation
  imports DPLL_CDCL_W_Implementation CDCL_W_Termination
       "HOL-Library.Code_Target_Numeral"
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
  "'v cdcl\<^sub>W_restart_ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option"

abbreviation raw_trail :: "'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> 'a" where
"raw_trail \<equiv> (\<lambda>(M, _). M)"

abbreviation raw_cons_trail :: "'a \<Rightarrow> 'a list \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> 'a list \<times> 'b \<times> 'c \<times> 'd"
  where
"raw_cons_trail \<equiv> (\<lambda>L (M, S). (L#M, S))"

abbreviation raw_tl_trail :: "'a list \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> 'a list \<times> 'b \<times> 'c \<times> 'd" where
"raw_tl_trail \<equiv> (\<lambda>(M, S). (tl M, S))"

abbreviation raw_init_clss :: "'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> 'b" where
"raw_init_clss \<equiv> \<lambda>(M, N, _). N"

abbreviation raw_learned_clss :: "'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> 'c" where
"raw_learned_clss \<equiv> \<lambda>(M, N, U, _). U"

abbreviation raw_conflicting :: "'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> 'd" where
"raw_conflicting \<equiv> \<lambda>(M, N, U, D). D"

abbreviation raw_update_conflicting :: "'d \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> 'a \<times> 'b \<times> 'c \<times> 'd"
  where
"raw_update_conflicting \<equiv> \<lambda>S (M, N, U, _).  (M, N, U, S)"

abbreviation "S0_cdcl\<^sub>W_restart N \<equiv> (([], N, {#}, None):: 'v cdcl\<^sub>W_restart_state)"

abbreviation raw_add_learned_clss where
"raw_add_learned_clss \<equiv> \<lambda>C (M, N, U, S). (M, N, {#C#} + U, S)"

abbreviation raw_remove_cls where
"raw_remove_cls \<equiv> \<lambda>C (M, N, U, S). (M, removeAll_mset C N, removeAll_mset C U, S)"

lemma raw_trail_conv: "raw_trail (M, N, U, D) = M" and
  clauses_conv: "raw_init_clss (M, N, U, D) = N" and
  raw_learned_clss_conv: "raw_learned_clss (M, N, U, D) = U" and
  raw_conflicting_conv: "raw_conflicting (M, N, U, D) = D"
  by auto

lemma state_conv:
  "S = (raw_trail S, raw_init_clss S, raw_learned_clss S, raw_conflicting S)"
  by (cases S) auto

definition state where
\<open>state S = (raw_trail S, raw_init_clss S, raw_learned_clss S, raw_conflicting S, ())\<close>

interpretation state\<^sub>W
  "(=)"
  state
  raw_trail raw_init_clss raw_learned_clss raw_conflicting
  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, U, S). (M, N, add_mset C U, S)"
  "\<lambda>C (M, N, U, S). (M, removeAll_mset C N, removeAll_mset C U, S)"
  "\<lambda>D (M, N, U, _). (M, N, U, D)"
  "\<lambda>N. ([], N, {#}, None)"
  by unfold_locales (auto simp: state_def)

declare state_simp[simp del]

interpretation conflict_driven_clause_learning\<^sub>W
  "(=)" state
  raw_trail raw_init_clss raw_learned_clss
  raw_conflicting
  "\<lambda>L (M, S). (L # M, S)"
  "\<lambda>(M, S). (tl M, S)"
  "\<lambda>C (M, N, U, S). (M, N, add_mset C U, S)"
  "\<lambda>C (M, N, U, S). (M, removeAll_mset C N, removeAll_mset C U, S)"
  "\<lambda>D (M, N, U, _). (M, N, U, D)"
  "\<lambda>N. ([], N, {#}, None)"
  by unfold_locales auto

declare clauses_def[simp]

lemma reduce_trail_to_empty_trail[simp]:
  "reduce_trail_to F ([], aa, ab, b) = ([], aa, ab, b)"
  using reduce_trail_to.simps by auto

lemma reduce_trail_to':
  "reduce_trail_to F S =
    ((if length (raw_trail S) \<ge> length F
    then drop (length (raw_trail S) - length F) (raw_trail S)
    else []), raw_init_clss S, raw_learned_clss S, raw_conflicting S)"
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


subsubsection \<open>Definition of the rules\<close>

paragraph \<open>Types\<close>
lemma true_raw_init_clss_remdups[simp]:
  "I \<Turnstile>s (mset \<circ> remdups) ` N \<longleftrightarrow>  I \<Turnstile>s mset ` N"
  by (simp add: true_clss_def)

lemma true_clss_raw_remdups_mset_mset[simp]:
  \<open>I \<Turnstile>s (\<lambda>L. remdups_mset (mset L)) ` N' \<longleftrightarrow> I \<Turnstile>s mset ` N'\<close>
  by (simp add: true_clss_def)

declare satisfiable_carac[iff del]
lemma satisfiable_mset_remdups[simp]:
  "satisfiable ((mset \<circ> remdups) ` N) \<longleftrightarrow> satisfiable (mset ` N)"
  "satisfiable ((\<lambda>L. remdups_mset (mset L)) ` N') \<longleftrightarrow> satisfiable (mset ` N')"
  unfolding satisfiable_carac[symmetric] by simp_all

type_synonym 'v cdcl\<^sub>W_restart_state_inv_st = "('v, 'v literal list) ann_lit list \<times>
  'v literal list list \<times> 'v literal list list \<times> 'v literal list option"

text \<open>We need some functions to convert between our abstract state @{typ "'v cdcl\<^sub>W_restart_state"}
  and the concrete state @{typ "'v cdcl\<^sub>W_restart_state_inv_st"}.\<close>

fun convert :: "('a, 'c list) ann_lit \<Rightarrow> ('a, 'c multiset) ann_lit" where
"convert (Propagated L C) = Propagated L (mset C)" |
"convert (Decided K) = Decided K"

abbreviation convertC :: "'a list option \<Rightarrow> 'a multiset option" where
"convertC \<equiv> map_option mset"

lemma convert_Propagated[elim!]:
  "convert z = Propagated L C \<Longrightarrow> (\<exists>C'. z = Propagated L C' \<and> C = mset C')"
  by (cases z) auto

lemma is_decided_convert[simp]: "is_decided (convert x) = is_decided x"
  by (cases x) auto

lemma is_decided_convert_is_decided[simp]: \<open>(is_decided \<circ> convert) = (is_decided)\<close>
  by auto

lemma get_level_map_convert[simp]:
  "get_level (map convert M) x = get_level M x"
  by (induction M rule: ann_lit_list_induct) (auto simp: comp_def get_level_def)

lemma get_maximum_level_map_convert[simp]:
  "get_maximum_level (map convert M) D = get_maximum_level M D"
  by (induction D) (auto simp add: get_maximum_level_add_mset)

lemma count_decided_convert[simp]:
  \<open>count_decided (map convert M) = count_decided M\<close>
  by (auto simp: count_decided_def)

lemma atm_lit_of_convert[simp]:
  "lit_of (convert x) =  lit_of x"
  by (cases x) auto

lemma no_dup_convert[simp]:
  \<open>no_dup (map convert M) = no_dup M\<close>
  by (auto simp: no_dup_def image_image comp_def)

text \<open>Conversion function\<close>
fun toS :: "'v cdcl\<^sub>W_restart_state_inv_st \<Rightarrow> 'v cdcl\<^sub>W_restart_state" where
"toS (M, N, U, C) = (map convert M, mset (map mset N),  mset (map mset U), convertC C)"

text \<open>Definition an abstract type\<close>
typedef 'v cdcl\<^sub>W_restart_state_inv =  "{S::'v cdcl\<^sub>W_restart_state_inv_st. cdcl\<^sub>W_all_struct_inv (toS S)}"
  morphisms rough_state_of state_of
proof
  show "([],[], [], None) \<in> {S. cdcl\<^sub>W_all_struct_inv (toS S)}"
    by (auto simp add: cdcl\<^sub>W_all_struct_inv_def)
qed

instantiation cdcl\<^sub>W_restart_state_inv :: (type) equal
begin
definition equal_cdcl\<^sub>W_restart_state_inv :: "'v cdcl\<^sub>W_restart_state_inv \<Rightarrow>
  'v cdcl\<^sub>W_restart_state_inv \<Rightarrow> bool" where
 "equal_cdcl\<^sub>W_restart_state_inv S S' = (rough_state_of S = rough_state_of S')"
instance
  by standard (simp add: rough_state_of_inject equal_cdcl\<^sub>W_restart_state_inv_def)
end

lemma lits_of_map_convert[simp]: "lits_of_l (map convert M) = lits_of_l M"
  by (induction M rule: ann_lit_list_induct) simp_all


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
  shows "propagate (toS (M, N, U, None)) (toS (Propagated L C # M, N, U, None))"
  using assms
  by (auto dest!: find_first_unit_clause_some simp add: propagate.simps
    intro!: exI[of _ "mset C - {#L#}"])


subsubsection \<open>The Transitions\<close>

paragraph \<open>Propagate\<close>
definition do_propagate_step :: \<open>'v cdcl\<^sub>W_restart_state_inv_st \<Rightarrow> 'v cdcl\<^sub>W_restart_state_inv_st\<close> where
"do_propagate_step S =
  (case S of
    (M, N, U, None) \<Rightarrow>
      (case find_first_unit_clause (N @ U) M of
        Some (L, C) \<Rightarrow> (Propagated L C # M, N, U, None)
      | None \<Rightarrow> (M, N, U, None))
  | S \<Rightarrow> S)"

lemma do_propagate_step:
  "do_propagate_step S \<noteq> S \<Longrightarrow> propagate (toS S) (toS (do_propagate_step S))"
  apply (cases S, cases "raw_conflicting S")
  using find_first_unit_clause_some_is_propagate[of "raw_init_clss S" "raw_learned_clss S" "raw_trail S"]
  by (auto simp add: do_propagate_step_def split: option.splits)

lemma do_propagate_step_option[simp]:
  "raw_conflicting S \<noteq> None \<Longrightarrow> do_propagate_step S = S"
  unfolding do_propagate_step_def by (cases S, cases "raw_conflicting S") auto

lemma do_propagate_step_no_step:
  assumes prop_step: "do_propagate_step S = S"
  shows "no_step propagate (toS S)"
proof (standard, standard)
  fix T
  assume "propagate (toS S) T"
  then obtain M N U C L E where
    toSS: "toS S = (M, N, U, None)" and
    LE: "L \<in># E" and
    T: "T = (Propagated L E # M, N, U, None)" and
    MC: "M \<Turnstile>as CNot C" and
    undef: "undefined_lit M L" and
    CL: "C + {#L#} \<in># N + U"
    apply - by (cases "toS S") (auto elim!: propagateE)
  let ?M = "raw_trail S"
  let ?N = "raw_init_clss S"
  let ?U = "raw_learned_clss S"
  let ?D = "None"
  have S: "S = (?M, ?N, ?U, ?D)"
    using toSS by (cases S, cases "raw_conflicting S") simp_all
  have S: "toS S = toS (?M, ?N, ?U, ?D)"
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
    using DCL by (metis add_mset_add_single ex_mset list.simps(15) set_mset_add_mset_insert
        set_mset_mset)
  have "find_first_unit_clause (?N @ ?U) ?M \<noteq> None"
    apply (rule find_first_unit_clause_none[of D "?N @ ?U" ?M L, OF D])
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
     (auto split: if_split_asm simp: lits_of_l_unfold)

lemma find_conflict_None:
  "find_conflict M Ns = None \<longleftrightarrow> (\<forall>N \<in> set Ns. \<not>M \<Turnstile>as CNot (mset N))"
  by (induction Ns) (auto simp: lits_of_l_unfold)

lemma find_conflict_None_no_confl:
  "find_conflict M (N@U) = None \<longleftrightarrow> no_step conflict (toS (M, N, U, None))"
  by (auto simp add: find_conflict_None conflict.simps)

definition do_conflict_step :: \<open>'v cdcl\<^sub>W_restart_state_inv_st \<Rightarrow> 'v cdcl\<^sub>W_restart_state_inv_st\<close> where
"do_conflict_step S =
  (case S of
    (M, N, U, None) \<Rightarrow>
      (case find_conflict M (N @ U) of
        Some a \<Rightarrow> (M, N, U, Some a)
      | None \<Rightarrow> (M, N, U, None))
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
  using find_conflict_None_no_confl[of "raw_trail S" "raw_init_clss S" "raw_learned_clss S"]
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

lemma cdcl\<^sub>W_all_struct_inv_rough_state[simp]: "cdcl\<^sub>W_all_struct_inv (toS (rough_state_of S))"
  using rough_state_of by auto

lemma [simp]: "cdcl\<^sub>W_all_struct_inv (toS S) \<Longrightarrow> rough_state_of (state_of S) = S"
  by (simp add: state_of_inverse)


paragraph \<open>Skip\<close>
fun do_skip_step :: "'v cdcl\<^sub>W_restart_state_inv_st \<Rightarrow> 'v cdcl\<^sub>W_restart_state_inv_st" where
"do_skip_step (Propagated L C # Ls, N, U, Some D) =
  (if -L \<notin> set D \<and> D \<noteq> []
  then (Ls, N, U, Some D)
  else (Propagated L C #Ls, N, U, Some D))" |
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
  "do_skip_step S = (a, b, c, None) \<longleftrightarrow> S = (a, b, c, None)"
  by (cases S rule: do_skip_step.cases) auto


paragraph \<open>Resolve\<close>
fun maximum_level_code:: "'a literal list \<Rightarrow> ('a, 'a literal list) ann_lit list \<Rightarrow> nat"
  where
"maximum_level_code [] _ = 0" |
"maximum_level_code (L # Ls) M = max (get_level M L) (maximum_level_code Ls M)"

lemma maximum_level_code_eq_get_maximum_level[code, simp]:
  "maximum_level_code D M = get_maximum_level M (mset D)"
  by (induction D) (auto simp add: get_maximum_level_add_mset)

fun do_resolve_step :: "'v cdcl\<^sub>W_restart_state_inv_st \<Rightarrow> 'v cdcl\<^sub>W_restart_state_inv_st" where
"do_resolve_step (Propagated L C # Ls, N, U, Some D) =
  (if -L \<in> set D \<and> maximum_level_code (remove1 (-L) D) (Propagated L C # Ls) = count_decided Ls
  then (Ls, N, U, Some (remdups (remove1 L C @ remove1 (-L) D)))
  else (Propagated L C # Ls, N, U, Some D))" |
"do_resolve_step S = S"

lemma do_resolve_step:
  "cdcl\<^sub>W_all_struct_inv (toS S) \<Longrightarrow> do_resolve_step S \<noteq> S
  \<Longrightarrow> resolve (toS S) (toS (do_resolve_step S))"
proof (induction S rule: do_resolve_step.induct)
  case (1 L C M N U D)
  then have
    "- L \<in> set D" and
    M: "maximum_level_code (remove1 (-L) D) (Propagated L C # M) = count_decided M"
    by (cases "mset D - {#- L#} = {#}",
        auto dest!: get_maximum_level_exists_lit_of_max_level[of _ "Propagated L C # M"]
        split: if_split_asm)+
  have "every_mark_is_a_conflict (toS (Propagated L C # M, N, U, Some D))"
    using 1(1) unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def by fast
  then have "L \<in> set C" by fastforce
  then obtain C' where C: "mset C = add_mset L C'"
    by (metis in_multiset_in_set insert_DiffM)
  obtain D' where D: "mset D = add_mset (-L) D'"
    using \<open>- L \<in> set D\<close> by (metis in_multiset_in_set insert_DiffM)
  have D'L:  "D' + {#- L#} - {#-L#} = D'" by (auto simp add: multiset_eq_iff)

  have CL: "mset C - {#L#} + {#L#} = mset C" using \<open>L \<in> set C\<close> by (auto simp add: multiset_eq_iff)
  have "get_maximum_level (Propagated L (C' + {#L#}) # map convert M) D' = count_decided M"
    using M[simplified] unfolding maximum_level_code_eq_get_maximum_level C[symmetric] CL
    by (metis D D'L \<open>add_mset L C' = mset C\<close> add_mset_add_single convert.simps(1)
        get_maximum_level_map_convert list.simps(9))
  then have
    "resolve
       (map convert (Propagated L C # M), mset `# mset N, mset `# mset U, Some (mset D))
       (map convert M, mset `# mset N, mset `# mset U,
         Some (((mset D - {#-L#}) \<union># (mset C - {#L#}))))"
    unfolding resolve.simps
      by (simp add: C D)
  moreover have
    "(map convert (Propagated L C # M), mset `# mset N, mset `# mset U, Some (mset D))
     = toS (Propagated L C # M, N, U, Some D)"
    by auto
  moreover
    have "distinct_mset (mset C)" and "distinct_mset (mset D)"
      using \<open>cdcl\<^sub>W_all_struct_inv (toS (Propagated L C # M, N, U, Some D))\<close>
      unfolding cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def
      by auto
    then have "(mset C - {#L#}) \<union># (mset D - {#- L#}) =
      remdups_mset (mset C - {#L#} + (mset D - {#- L#}))"
      by (auto simp: distinct_mset_rempdups_union_mset)
    then have "(map convert M, mset `# mset N, mset `# mset U,
    Some ((mset D - {#- L#}) \<union># (mset C - {#L#})))
    = toS (do_resolve_step (Propagated L C # M, N, U, Some D))"
    using \<open>- L \<in> set D\<close> M by (auto simp: ac_simps)
  ultimately show ?case
    by simp
qed auto

lemma do_resolve_step_no:
  "do_resolve_step S = S \<Longrightarrow> no_step resolve (toS S)"
  apply (cases S; cases "hd (raw_trail S)";cases "raw_trail S"; cases "raw_conflicting S")
  by (auto
    elim!: resolveE split: if_split_asm
    dest!: union_single_eq_member
    simp del: in_multiset_in_set get_maximum_level_map_convert
    simp: get_maximum_level_map_convert[symmetric] count_decided_def)

lemma rough_state_of_state_of_resolve[simp]:
  "cdcl\<^sub>W_all_struct_inv (toS S) \<Longrightarrow>
    rough_state_of (state_of (do_resolve_step S)) = do_resolve_step S"
  apply (rule state_of_inverse)
  apply (cases "do_resolve_step S = S")
   apply (simp; fail)
  by (metis (mono_tags, lifting) bj cdcl\<^sub>W_all_struct_inv_inv do_resolve_step mem_Collect_eq other
        resolve)

lemma do_resolve_step_raw_trail_is_None[iff]:
  "do_resolve_step S = (a, b, c, None) \<longleftrightarrow> S = (a, b, c, None)"
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
    inv: "cdcl\<^sub>W_all_struct_inv (toS S)"
  shows "backtrack (toS S) (toS (do_backtrack_step S))"
proof (cases S, cases "raw_conflicting S", goal_cases)
  case (1 M N U E)
  then show ?case using db by auto
next
  case (2 M N U E C) note S = this(1) and confl = this(2)
  have E: "E = Some C" using S confl by auto

  obtain L j where fd: "find_level_decomp M C [] (count_decided M) = Some (L, j)"
    using db unfolding S E by (cases C) (auto split: if_split_asm option.splits list.splits
        annotated_lit.splits)
  have
    "L \<in> set C" and
    j: "get_maximum_level M (mset (remove1 L C)) = j" and
    levL: "get_level M L = count_decided M"
    using find_level_decomp_some[OF fd] by auto
  obtain C' where C: "mset C = add_mset L (mset C')"
    using \<open>L \<in> set C\<close> by (metis ex_mset in_multiset_in_set insert_DiffM)
  obtain M2 where M2: "bt_cut j M = Some M2"
    using db fd unfolding S E by (auto split: option.splits)
  have "no_dup M"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def S
    by (auto simp: comp_def)
  then obtain M1 K c where
    M1: "M2 = Decided K # M1" and lev_K: "get_level M K = j + 1" and
    c: "M = c @ M2"
    using bt_cut_some_decomp[OF _ M2] by (cases M2) auto
  have "j \<le> count_decided M" unfolding c j[symmetric]
    by (metis (mono_tags, lifting) count_decided_ge_get_maximum_level)
  have max_l_j: "maximum_level_code C' M = j"
    using db fd M2 C unfolding S E by (auto
        split: option.splits list.splits annotated_lit.splits
        dest!: find_level_decomp_some)[1]
  have "get_maximum_level M (mset C) \<ge> count_decided M"
    using \<open>L \<in> set C\<close> levL get_maximum_level_ge_get_level by (metis set_mset_mset)
  moreover have "get_maximum_level M (mset C) \<le> count_decided M"
    using count_decided_ge_get_maximum_level by blast
  ultimately have max_lev_count_dec: "get_maximum_level M (mset C) = count_decided M" by auto

  have clss_C: \<open>clauses (toS S) \<Turnstile>pm mset C\<close> and
    M_C: \<open>M \<Turnstile>as CNot (mset C)\<close> and
    lev_inv: "cdcl\<^sub>W_M_level_inv (toS S)"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_alt_def S E
      cdcl\<^sub>W_conflicting_def
    by auto
  obtain M2' where M2': "(M2, M2') \<in> set (get_all_ann_decomposition M)"
    using bt_cut_in_get_all_ann_decomposition[OF \<open>no_dup M\<close> M2] by metis
  have decomp:
    "(Decided K # (map convert M1),
      (map convert M2')) \<in>
      set (get_all_ann_decomposition (map convert M))"
    using imageI[of _ _ "\<lambda>(a, b). (map convert a, map convert b)", OF M2'] j
    unfolding S E M1 by (simp add: get_all_ann_decomposition_map_convert)
  have decomp':
    "(Decided K # (map convert M1),
      (map convert M2')) \<in>
      set (get_all_ann_decomposition (raw_trail (toS S)))"
    using imageI[of _ _ "\<lambda>(a, b). (map convert a, map convert b)", OF M2'] j
    unfolding S E M1 by (simp add: get_all_ann_decomposition_map_convert)

  show ?case
    apply (rule backtrack\<^sub>W_rule[of \<open>toS S\<close> L \<open>remove1_mset L (mset C)\<close> K \<open>map convert M1\<close> \<open>map convert M2'\<close>
          j])
    subgoal using \<open>L \<in> set C\<close> unfolding S E M1 by auto
    subgoal using M2' decomp unfolding S by auto
    subgoal using levL unfolding S E M1 by auto
    subgoal using \<open>L \<in> set C\<close> levL \<open>get_maximum_level M (mset C) = count_decided M\<close>
      unfolding S E M1 by auto
    subgoal using j unfolding S E M1 by auto
    subgoal using \<open>L \<in> set C\<close> lev_K unfolding S E M1 by auto
    subgoal using S confl fd M2 M1 decomp \<open>L \<in> set C\<close> by (auto simp: reduce_trail_to' M2 c)
    subgoal using inv unfolding cdcl\<^sub>W_all_struct_inv_def S by fast
    subgoal using inv unfolding cdcl\<^sub>W_all_struct_inv_def S by fast
    subgoal using inv unfolding cdcl\<^sub>W_all_struct_inv_def S by fast
    done
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

declare conflict_is_false_with_level_def[simp del]

lemma do_backtrack_step_no:
  assumes
    db: "do_backtrack_step S = S" and
    inv: "cdcl\<^sub>W_all_struct_inv (toS S)" and
    ns: \<open>no_step skip (toS S)\<close> \<open>no_step resolve (toS S)\<close>
  shows "no_step backtrack (toS S)"
proof (rule ccontr, cases S, cases "raw_conflicting S", goal_cases)
  case 1
  then show ?case using db by (auto split: option.splits elim: backtrackE)
next
  case (2 M N U E C) note bt = this(1) and S = this(2) and confl = this(3)
  have E: "E = Some C" using S confl by auto
  obtain T' where \<open>simple_backtrack (toS S) T'\<close>
    using no_analyse_backtrack_Ex_simple_backtrack[of \<open>toS S\<close>]
      bt inv ns unfolding cdcl\<^sub>W_all_struct_inv_def by meson
  then obtain K j M1 M2 L D where
    CE: "map_option mset (raw_conflicting S) = Some (add_mset L D)" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (raw_trail S))" and
    levL: "get_level (raw_trail S) L =  count_decided (raw_trail (toS S))" and
    k: "get_level (raw_trail S) L = get_maximum_level (raw_trail S) (add_mset L D)" and
    j: "get_maximum_level (raw_trail S) D \<equiv> j" and
    lev_K: "get_level (raw_trail S) K = Suc j"
    apply clarsimp
    apply (elim simple_backtrackE)
    apply (cases S)
    by (auto simp add: get_all_ann_decomposition_map_convert reduce_trail_to
      Decided_convert_iff)
  obtain c where c: "raw_trail S = c @ M2 @ Decided K # M1"
    using decomp by blast
  have n_d: "no_dup M"
    using inv S unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
    by (auto simp: comp_def)
  then have "count_decided (raw_trail (toS S)) > j"
    using j count_decided_ge_get_maximum_level[of "raw_trail S" "D"]
    count_decided_ge_get_level[of "raw_trail S" K] decomp lev_K
    unfolding k S by (auto simp: get_all_ann_decomposition_map_convert)
  have CD: "mset C =  add_mset L D"
    using CE confl by auto
  then have L_C: \<open>L \<in> set C\<close>
    using set_mset_mset by fastforce
  have "find_level_decomp M C [] (count_decided (raw_trail (toS S))) \<noteq> None"
    apply rule
    apply (drule find_level_decomp_none[of _ _ _ _ L \<open>remove1 L C\<close>])
    using L_C CD \<open>count_decided (raw_trail (toS S)) > j\<close> mset_eq_setD S levL unfolding k[symmetric] j[symmetric]
    by (auto simp: ac_simps)

  then obtain L' j' where fd_some: "find_level_decomp M C [] (count_decided (raw_trail (toS S))) = Some (L', j')"
    by (cases "find_level_decomp M C [] (count_decided (raw_trail (toS S)))") auto
  have L': "L' = L"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "L' \<in># D"
      using fd_some find_level_decomp_some set_mset_mset
      by (metis CD insert_iff set_mset_add_mset_insert)
    then have "get_level M L' \<le> get_maximum_level M D"
      using get_maximum_level_ge_get_level by blast
    then show False
      using \<open>count_decided (raw_trail (toS S)) > j\<close> j
        find_level_decomp_some[OF fd_some] S by auto
  qed
  then have j': "j' = j" using find_level_decomp_some[OF fd_some] j S CD by auto

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
  show ?case using db n_d fd_some L' j' btc_none unfolding S E
    by (auto dest: bt_cut_some_decomp)
qed

lemma rough_state_of_state_of_backtrack[simp]:
  assumes inv: "cdcl\<^sub>W_all_struct_inv (toS S)"
  shows "rough_state_of (state_of (do_backtrack_step S)) = do_backtrack_step S"
proof (rule state_of_inverse)
  consider
    (step) "backtrack (toS S) (toS (do_backtrack_step S))" |
     (0) "do_backtrack_step S = S"
    using do_backtrack_step inv by blast
  then show "do_backtrack_step S \<in> {S. cdcl\<^sub>W_all_struct_inv (toS S)}"
  proof cases
    case 0
    thus ?thesis using inv by simp
  next
    case step
    then show ?thesis
      using inv
      by (auto dest!: cdcl\<^sub>W_restart.other cdcl\<^sub>W_o.bj cdcl\<^sub>W_bj.backtrack intro: cdcl\<^sub>W_all_struct_inv_inv)
  qed
qed


paragraph \<open>Decide\<close>
fun do_decide_step where
"do_decide_step (M, N, U, None) =
  (case find_first_unused_var N (lits_of_l M) of
    None \<Rightarrow> (M, N, U, None)
  | Some L \<Rightarrow> (Decided L # M, N, U,  None))" |
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
        b :: "'a literal list list" and c :: "'a literal list list" and
        e :: "'a literal list option"
  {
    fix a :: "('a, 'a literal list) ann_lit list" and
        b :: "'a literal list list" and c :: "'a literal list list" and
        x2 :: "'a literal" and m :: "'a literal list"
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

  assume "do_decide_step S \<noteq> S" and
     "S = (a, b, c, e)" and
     "raw_conflicting S = None"
  then show "decide (toS S) (toS (do_decide_step S))"
    using H H' by (auto split: option.splits simp: decide.simps defined_lit_map lits_of_def
      image_image atm_of_eq_atm_of dest!: find_first_unused_var_Some)
qed

lemma do_decide_step_no:
  "do_decide_step S = S \<Longrightarrow> no_step decide (toS S)"
  apply (cases S, cases "raw_conflicting S")
  apply (auto simp: atms_of_ms_mset_unfold Decided_Propagated_in_iff_in_lits_of_l lits_of_def
      dest!: atm_of_in_atm_of_set_in_uminus
      elim!: decideE
      split: option.splits)+
  using atm_of_eq_atm_of by blast+


lemma rough_state_of_state_of_do_decide_step[simp]:
  "cdcl\<^sub>W_all_struct_inv (toS S) \<Longrightarrow> rough_state_of (state_of (do_decide_step S)) = do_decide_step S"
proof (subst state_of_inverse, goal_cases)
  case 1
  then show ?case
    by (cases "do_decide_step S = S")
      (auto dest: do_decide_step decide other intro: cdcl\<^sub>W_all_struct_inv_inv)
qed simp

lemma rough_state_of_state_of_do_skip_step[simp]:
  "cdcl\<^sub>W_all_struct_inv (toS S) \<Longrightarrow> rough_state_of (state_of (do_skip_step S)) = do_skip_step S"
  apply (subst state_of_inverse, cases "do_skip_step S = S")
   apply simp
  by (blast dest: other skip bj do_skip_step cdcl\<^sub>W_all_struct_inv_inv)+


subsubsection \<open>Code generation\<close>

paragraph \<open>Type definition\<close>
text \<open>There are two invariants: one while applying conflict and propagate and one for the other
 rules\<close>

declare rough_state_of_inverse[simp add]
definition Con where
  "Con xs = state_of (if cdcl\<^sub>W_all_struct_inv (toS (fst xs, snd xs)) then xs
  else ([], [], [], None))"

lemma [code abstype]:
 "Con (rough_state_of S) = S"
  using rough_state_of[of S] unfolding Con_def by simp

definition do_cp_step' where
"do_cp_step' S = state_of (do_cp_step (rough_state_of S))"

typedef 'v cdcl\<^sub>W_restart_state_inv_from_init_state =
  "{S:: 'v cdcl\<^sub>W_restart_state_inv_st. cdcl\<^sub>W_all_struct_inv (toS S)
    \<and> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (S0_cdcl\<^sub>W_restart (raw_init_clss (toS S))) (toS S)}"
  morphisms rough_state_from_init_state_of state_from_init_state_of
proof
  show "([],[], [], None) \<in> {S. cdcl\<^sub>W_all_struct_inv (toS S)
    \<and> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (S0_cdcl\<^sub>W_restart (raw_init_clss (toS S))) (toS S)}"
    by (auto simp add: cdcl\<^sub>W_all_struct_inv_def)
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
  "ConI S = state_from_init_state_of (if cdcl\<^sub>W_all_struct_inv (toS (fst S, snd S))
    \<and> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (S0_cdcl\<^sub>W_restart (raw_init_clss (toS S))) (toS S) then S else ([], [], [], None))"

lemma [code abstype]:
  "ConI (rough_state_from_init_state_of S) = S"
  using rough_state_from_init_state_of[of S] unfolding ConI_def
  by (simp add: rough_state_from_init_state_of_inverse)

definition id_of_I_to:: "'v cdcl\<^sub>W_restart_state_inv_from_init_state \<Rightarrow> 'v cdcl\<^sub>W_restart_state_inv" where
"id_of_I_to S = state_of (rough_state_from_init_state_of S)"

lemma [code abstract]:
  "rough_state_of (id_of_I_to S) = rough_state_from_init_state_of S"
  unfolding id_of_I_to_def using rough_state_from_init_state_of[of S] by auto

lemma in_clauses_rough_state_of_is_distinct:
  "c\<in>set (raw_init_clss (rough_state_of S) @ raw_learned_clss (rough_state_of S)) \<Longrightarrow> distinct c"
  apply (cases "rough_state_of S")
  using rough_state_of[of S] by (auto simp add: distinct_mset_set_distinct cdcl\<^sub>W_all_struct_inv_def
    distinct_cdcl\<^sub>W_state_def)

paragraph \<open>The other rules\<close>
fun do_if_not_equal where
"do_if_not_equal [] S = S" |
"do_if_not_equal (f # fs) S =
  (let T = f S in
   if T \<noteq> S then T else do_if_not_equal fs S)"

fun do_cdcl_step where
"do_cdcl_step S =
  do_if_not_equal [do_conflict_step, do_propagate_step, do_skip_step, do_resolve_step,
  do_backtrack_step, do_decide_step] S"

lemma do_cdcl_step:
  assumes inv: "cdcl\<^sub>W_all_struct_inv (toS S)" and
  st: "do_cdcl_step S \<noteq> S"
  shows "cdcl\<^sub>W_stgy (toS S) (toS (do_cdcl_step S))"
  using st by (auto simp add: do_skip_step do_resolve_step do_backtrack_step do_decide_step
    do_conflict_step
    do_propagate_step do_conflict_step_no_step do_propagate_step_no_step
    cdcl\<^sub>W_stgy.intros cdcl\<^sub>W_bj.intros cdcl\<^sub>W_o.intros inv Let_def)

lemma do_cdcl_step_no:
  assumes inv: "cdcl\<^sub>W_all_struct_inv (toS S)" and
  st: "do_cdcl_step S = S"
  shows "no_step cdcl\<^sub>W (toS S)"
  using st inv by (auto split: if_split_asm elim: cdcl\<^sub>W_bjE
    simp add: Let_def cdcl\<^sub>W_bj.simps cdcl\<^sub>W.simps do_conflict_step
    do_propagate_step do_conflict_step_no_step do_propagate_step_no_step
    elim!: cdcl\<^sub>W_o.cases
    dest!: do_skip_step_no do_resolve_step_no do_backtrack_step_no do_decide_step_no)

lemma rough_state_of_state_of_do_cdcl_step[simp]:
  "rough_state_of (state_of (do_cdcl_step (rough_state_of S))) = do_cdcl_step (rough_state_of S)"
proof (cases "do_cdcl_step (rough_state_of S) = rough_state_of S")
  case True
  then show ?thesis by simp
next
  case False
  have "cdcl\<^sub>W (toS (rough_state_of S)) (toS (do_cdcl_step (rough_state_of S)))"
    using False cdcl\<^sub>W_all_struct_inv_rough_state cdcl\<^sub>W_stgy_cdcl\<^sub>W do_cdcl_step by blast
  then have "cdcl\<^sub>W_all_struct_inv (toS (do_cdcl_step (rough_state_of S)))"
    using cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_all_struct_inv_rough_state cdcl\<^sub>W_cdcl\<^sub>W_restart by blast
  then show ?thesis
    by (simp add: CollectI state_of_inverse)
qed

definition do_cdcl\<^sub>W_stgy_step :: "'v cdcl\<^sub>W_restart_state_inv \<Rightarrow> 'v cdcl\<^sub>W_restart_state_inv" where
"do_cdcl\<^sub>W_stgy_step S =
  state_of (do_cdcl_step (rough_state_of S))"

lemma rough_state_of_do_cdcl\<^sub>W_stgy_step[code abstract]:
 "rough_state_of (do_cdcl\<^sub>W_stgy_step S) = do_cdcl_step (rough_state_of S)"
 apply (cases "do_cdcl_step (rough_state_of S) = rough_state_of S")
   unfolding do_cdcl\<^sub>W_stgy_step_def apply simp
 using do_cdcl_step[of "rough_state_of S"] rough_state_of_state_of_do_cdcl_step by blast

definition do_cdcl\<^sub>W_stgy_step' where
"do_cdcl\<^sub>W_stgy_step' S = state_from_init_state_of (rough_state_of (do_cdcl\<^sub>W_stgy_step (id_of_I_to S)))"


paragraph \<open>Correction of the transformation\<close>
lemma do_cdcl\<^sub>W_stgy_step:
  assumes "do_cdcl\<^sub>W_stgy_step S \<noteq> S"
  shows "cdcl\<^sub>W_stgy (toS (rough_state_of S)) (toS (rough_state_of (do_cdcl\<^sub>W_stgy_step S)))"
proof -
  have "do_cdcl_step (rough_state_of S) \<noteq> rough_state_of S"
    by (metis (no_types) assms do_cdcl\<^sub>W_stgy_step_def rough_state_of_inject
      rough_state_of_state_of_do_cdcl_step)
  then have "cdcl\<^sub>W_stgy (toS (rough_state_of S)) (toS (do_cdcl_step (rough_state_of S)))"
    using cdcl\<^sub>W_all_struct_inv_rough_state do_cdcl_step by blast
  then show ?thesis
    by (metis (no_types) do_cdcl\<^sub>W_stgy_step_def rough_state_of_state_of_do_cdcl_step)
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

lemma do_cp_step_neq_raw_trail_increase:
  "\<exists>c. raw_trail (do_cp_step S) = c @ raw_trail S \<and> (\<forall>m \<in> set c. \<not> is_decided m)"
  by (cases S, cases "raw_conflicting S")
     (auto simp add: do_cp_step_def do_conflict_step_def do_propagate_step_def split: option.splits)

lemma do_cp_step_raw_conflicting:
  "raw_conflicting (rough_state_of S) \<noteq> None \<Longrightarrow> do_cp_step' S = S"
  unfolding do_cp_step'_def do_cp_step_def by simp

lemma do_decide_step_not_raw_conflicting_one_more_decide:
  assumes
    "raw_conflicting S = None" and
    "do_decide_step S \<noteq> S"
  shows "Suc (length (filter is_decided (raw_trail S)))
    = length (filter is_decided (raw_trail (do_decide_step S)))"
  using assms by (cases S) (auto simp: Let_def split: if_split_asm option.splits
     dest!: find_first_unused_var_Some_not_all_incl)

lemma do_decide_step_not_raw_conflicting_one_more_decide_bt:
  assumes "raw_conflicting S \<noteq> None" and
  "do_decide_step S \<noteq> S"
  shows "length (filter is_decided (raw_trail S)) < length (filter is_decided (raw_trail (do_decide_step S)))"
  using assms by (cases S, cases "raw_conflicting S")
    (auto simp add: Let_def split: if_split_asm option.splits)

lemma count_decided_raw_trail_toS:
  "count_decided (raw_trail (toS S)) = count_decided (raw_trail S)"
  by (cases S) (auto simp: comp_def)

lemma rough_state_of_state_of_do_skip_step_rough_state_of[simp]:
  "rough_state_of (state_of (do_skip_step (rough_state_of S))) = do_skip_step (rough_state_of S)"
  using cdcl\<^sub>W_all_struct_inv_rough_state rough_state_of_state_of_do_skip_step by blast

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
  apply (cases S rule: do_backtrack_step.cases)
   apply (auto simp add: Let_def split: option.splits list.splits
      (*   annotated_lit.split *)) \<comment> \<open>TODO splitting should solve the goal\<close>
  apply (rename_tac dec tr)
  by (case_tac dec) auto

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
  apply (auto split: option.split list.splits (* annotated_lit.splits *)
     simp: comp_def
     dest!: bt_cut_in_get_all_ann_decomposition) \<comment> \<open>TODO splitting should solve the goal\<close>
  apply (rename_tac dec tr tra)
  by (case_tac dec) auto


lemma do_resolve_step_eq_iff_raw_trail_eq:
  "do_resolve_step S = S \<longleftrightarrow> raw_trail (do_resolve_step S) = raw_trail S"
  by (cases S rule: do_resolve_step.cases) auto

lemma do_cdcl\<^sub>W_stgy_step_no:
  assumes S: "do_cdcl\<^sub>W_stgy_step S = S"
  shows "no_step cdcl\<^sub>W_stgy (toS (rough_state_of S))"
proof -
  have "do_cdcl_step (rough_state_of S) = rough_state_of S"
    by (metis assms rough_state_of_do_cdcl\<^sub>W_stgy_step)
  then show ?thesis
    using cdcl\<^sub>W_all_struct_inv_rough_state cdcl\<^sub>W_stgy_cdcl\<^sub>W do_cdcl_step_no by blast
qed

lemma toS_rough_state_of_state_of_rough_state_from_init_state_of[simp]:
  "toS (rough_state_of (state_of (rough_state_from_init_state_of S)))
    = toS (rough_state_from_init_state_of S)"
  using rough_state_from_init_state_of[of S] by (auto simp add: state_of_inverse)

lemma cdcl\<^sub>W_stgy_is_rtranclp_cdcl\<^sub>W_restart:
  "cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
  by (simp add: cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W_restart rtranclp_unfold)

lemma cdcl\<^sub>W_stgy_init_raw_init_clss:
  "cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_M_level_inv S \<Longrightarrow> raw_init_clss S = raw_init_clss T"
  using cdcl\<^sub>W_stgy_no_more_init_clss by blast

lemma clauses_toS_rough_state_of_do_cdcl\<^sub>W_stgy_step[simp]:
  "raw_init_clss (toS (rough_state_of (do_cdcl\<^sub>W_stgy_step (state_of (rough_state_from_init_state_of S)))))
    = raw_init_clss (toS (rough_state_from_init_state_of S))" (is "_ = raw_init_clss (toS ?S)")
  apply (cases "do_cdcl\<^sub>W_stgy_step (state_of ?S) = state_of ?S")
    apply simp
  by (metis cdcl\<^sub>W_stgy_no_more_init_clss do_cdcl\<^sub>W_stgy_step
    toS_rough_state_of_state_of_rough_state_from_init_state_of)

lemma rough_state_from_init_state_of_do_cdcl\<^sub>W_stgy_step'[code abstract]:
 "rough_state_from_init_state_of (do_cdcl\<^sub>W_stgy_step' S) =
   rough_state_of (do_cdcl\<^sub>W_stgy_step (id_of_I_to S))"
proof -
  let ?S = "(rough_state_from_init_state_of S)"
  have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (S0_cdcl\<^sub>W_restart (raw_init_clss (toS (rough_state_from_init_state_of S))))
    (toS (rough_state_from_init_state_of S))"
    using rough_state_from_init_state_of[of S] by auto
  moreover have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>*
                  (toS (rough_state_from_init_state_of S))
                  (toS (rough_state_of (do_cdcl\<^sub>W_stgy_step
                    (state_of (rough_state_from_init_state_of S)))))"
     using do_cdcl\<^sub>W_stgy_step[of "state_of ?S"]
     by (cases "do_cdcl\<^sub>W_stgy_step (state_of ?S) = state_of ?S") auto
  ultimately show ?thesis
    unfolding do_cdcl\<^sub>W_stgy_step'_def id_of_I_to_def
    by (auto intro!: state_from_init_state_of_inverse)
qed

paragraph \<open>All rules together\<close>
function do_all_cdcl\<^sub>W_stgy where
"do_all_cdcl\<^sub>W_stgy S =
  (let T = do_cdcl\<^sub>W_stgy_step' S in
  if T = S then S else do_all_cdcl\<^sub>W_stgy T)"
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
  have S: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (S0_cdcl\<^sub>W_restart (raw_init_clss (toS ?S))) (toS ?S)"
    using rough_state_from_init_state_of[of S] by auto
  moreover have "cdcl\<^sub>W_stgy (toS (rough_state_from_init_state_of S))
    (toS (rough_state_from_init_state_of T))"
  proof -
    have "\<And>c. rough_state_of (state_of (rough_state_from_init_state_of c)) =
        rough_state_from_init_state_of c"
      using rough_state_from_init_state_of state_of_inverse by fastforce
    then have diff: "do_cdcl\<^sub>W_stgy_step (state_of (rough_state_from_init_state_of S))
        \<noteq> state_of (rough_state_from_init_state_of S)"
      using ST T by (metis (no_types) id_of_I_to_def rough_state_from_init_state_of_inject
          rough_state_from_init_state_of_do_cdcl\<^sub>W_stgy_step')
    have "rough_state_of (do_cdcl\<^sub>W_stgy_step (state_of (rough_state_from_init_state_of S)))
        =  rough_state_from_init_state_of (do_cdcl\<^sub>W_stgy_step' S)"
      by (simp add: id_of_I_to_def rough_state_from_init_state_of_do_cdcl\<^sub>W_stgy_step')
    then show ?thesis
      using do_cdcl\<^sub>W_stgy_step T diff unfolding id_of_I_to_def do_cdcl\<^sub>W_stgy_step by fastforce
  qed
  moreover have invs: "cdcl\<^sub>W_all_struct_inv (toS (rough_state_from_init_state_of S))"
      using rough_state_from_init_state_of[of S] by auto
  moreover {
    have "cdcl\<^sub>W_all_struct_inv (S0_cdcl\<^sub>W_restart (raw_init_clss (toS (rough_state_from_init_state_of S))))"
      using invs by (cases "rough_state_from_init_state_of S")
         (auto simp add: cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def)
    then have \<open>no_smaller_propa (toS (rough_state_from_init_state_of S))\<close>
      using rtranclp_cdcl\<^sub>W_stgy_no_smaller_propa[OF S]
      by (auto simp: empty_trail_no_smaller_propa) }
  ultimately show ?case
    using tranclp_cdcl\<^sub>W_stgy_S0_decreasing
    by (auto intro!: cdcl\<^sub>W_stgy_step_decreasing[of ]
      simp del: cdcl\<^sub>W_restart_measure.simps)
qed

thm do_all_cdcl\<^sub>W_stgy.induct
lemma do_all_cdcl\<^sub>W_stgy_induct:
  "(\<And>S. (do_cdcl\<^sub>W_stgy_step' S \<noteq> S \<Longrightarrow> P (do_cdcl\<^sub>W_stgy_step' S)) \<Longrightarrow> P S) \<Longrightarrow> P a0"
 using do_all_cdcl\<^sub>W_stgy.induct by metis

lemma no_step_cdcl\<^sub>W_stgy_cdcl\<^sub>W_restart_all:
  fixes S :: "'a cdcl\<^sub>W_restart_state_inv_from_init_state"
  shows "no_step cdcl\<^sub>W_stgy (toS (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy S)))"
  apply (induction S rule: do_all_cdcl\<^sub>W_stgy_induct)
  apply (rename_tac S, case_tac "do_cdcl\<^sub>W_stgy_step' S \<noteq> S")
proof -
  fix Sa :: "'a cdcl\<^sub>W_restart_state_inv_from_init_state"
  assume a1: "\<not> do_cdcl\<^sub>W_stgy_step' Sa \<noteq> Sa"
  { fix pp
    have "(if True then Sa else do_all_cdcl\<^sub>W_stgy Sa) = do_all_cdcl\<^sub>W_stgy Sa"
      using a1 by auto
    then have "\<not> cdcl\<^sub>W_stgy (toS (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy Sa))) pp"
      using a1 by (metis (no_types) do_cdcl\<^sub>W_stgy_step_no id_of_I_to_def
        rough_state_from_init_state_of_do_cdcl\<^sub>W_stgy_step' rough_state_of_inverse) }
  then show "no_step cdcl\<^sub>W_stgy (toS (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy Sa)))"
    by fastforce
next
  fix Sa :: "'a cdcl\<^sub>W_restart_state_inv_from_init_state"
  assume a1: "do_cdcl\<^sub>W_stgy_step' Sa \<noteq> Sa
    \<Longrightarrow> no_step cdcl\<^sub>W_stgy (toS (rough_state_from_init_state_of
      (do_all_cdcl\<^sub>W_stgy (do_cdcl\<^sub>W_stgy_step' Sa))))"
  assume a2: "do_cdcl\<^sub>W_stgy_step' Sa \<noteq> Sa"
  have "do_all_cdcl\<^sub>W_stgy Sa = do_all_cdcl\<^sub>W_stgy (do_cdcl\<^sub>W_stgy_step' Sa)"
    by (metis (full_types) do_all_cdcl\<^sub>W_stgy.simps)
  then show "no_step cdcl\<^sub>W_stgy (toS (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy Sa)))"
    using a2 a1 by presburger
qed

lemma do_all_cdcl\<^sub>W_stgy_is_rtranclp_cdcl\<^sub>W_stgy:
  "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (toS (rough_state_from_init_state_of S))
    (toS (rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy S)))"
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
        using rough_state_from_init_state_of_do_cdcl\<^sub>W_stgy_step'
       by (simp add: id_of_I_to_def rough_state_from_init_state_of_do_cdcl\<^sub>W_stgy_step')
      have f3: "do_all_cdcl\<^sub>W_stgy S = do_all_cdcl\<^sub>W_stgy (do_cdcl\<^sub>W_stgy_step' S)"
        by (metis (full_types) do_all_cdcl\<^sub>W_stgy.simps)
      have "cdcl\<^sub>W_stgy (toS (rough_state_from_init_state_of S))
          (toS (rough_state_from_init_state_of (do_cdcl\<^sub>W_stgy_step' S)))
        = cdcl\<^sub>W_stgy (toS (rough_state_of (id_of_I_to S)))
          (toS (rough_state_of (do_cdcl\<^sub>W_stgy_step (id_of_I_to S))))"
        using rough_state_from_init_state_of_do_cdcl\<^sub>W_stgy_step'
        toS_rough_state_of_state_of_rough_state_from_init_state_of
        by (simp add: id_of_I_to_def rough_state_from_init_state_of_do_cdcl\<^sub>W_stgy_step')
      then show ?thesis
        using f3 f2 IH do_cdcl\<^sub>W_stgy_step by fastforce
    qed
qed

text \<open>Final theorem:\<close>
lemma DPLL_tot_correct:
  assumes
    r: "rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy (state_from_init_state_of
      (([], map remdups N, [], None)))) = S" and
    S: "(M', N', U', E) = toS S"
  shows "(E \<noteq> Some {#} \<and> satisfiable (set (map mset N)))
    \<or> (E = Some {#} \<and> unsatisfiable (set (map mset N)))"
proof -
  let ?N = "map remdups N"
  have inv: "cdcl\<^sub>W_all_struct_inv (toS ([], map remdups N, [], None))"
    unfolding cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def distinct_mset_set_def by auto
  then have S0: "rough_state_of (state_of ([], map remdups N, [], None))
    = ([], map remdups N, [], None)" by simp
  have 1: "full cdcl\<^sub>W_stgy (toS ([], ?N, [], None)) (toS S)"
    unfolding full_def apply rule
      using do_all_cdcl\<^sub>W_stgy_is_rtranclp_cdcl\<^sub>W_stgy[of
        "state_from_init_state_of ([], map remdups N, [], None)"] inv
        no_step_cdcl\<^sub>W_stgy_cdcl\<^sub>W_restart_all
        apply (auto simp del: do_all_cdcl\<^sub>W_stgy.simps simp: state_from_init_state_of_inverse
          r[symmetric] comp_def)[]
      using do_all_cdcl\<^sub>W_stgy_is_rtranclp_cdcl\<^sub>W_stgy[of
      "state_from_init_state_of ([], map remdups N, [], None)"] inv
      no_step_cdcl\<^sub>W_stgy_cdcl\<^sub>W_restart_all
      by (force simp: state_from_init_state_of_inverse r["symmetric"] comp_def)
  moreover have 2: "finite (set (map mset ?N))" by auto
  moreover have 3: "distinct_mset_set (set (map mset ?N))"
     unfolding distinct_mset_set_def by auto
  moreover
    have "cdcl\<^sub>W_all_struct_inv (toS S)"
      by (metis (no_types) cdcl\<^sub>W_all_struct_inv_rough_state r
        toS_rough_state_of_state_of_rough_state_from_init_state_of)
    then have cons: "consistent_interp (lits_of_l M')"
      unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def S[symmetric] by auto
  moreover
    have "raw_init_clss (toS ([], ?N, [], None)) = raw_init_clss (toS S)"
      apply (rule rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss)
      using 1 unfolding full_def by (auto simp add: rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
    then have N': "mset (map mset ?N) = N'"
      using S[symmetric] by auto
  have "(E \<noteq> Some {#} \<and> satisfiable (set (map mset ?N)))
    \<or> (E = Some {#} \<and> unsatisfiable (set (map mset ?N)))"
    using full_cdcl\<^sub>W_stgy_final_state_conclusive unfolding N' apply rule
        using 1 apply (simp; fail)
      using 3 apply (simp add: comp_def; fail)
     using S[symmetric] N' apply (auto; fail)[1]
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
"gene (Suc n) = map ((#) (Pos (Suc n))) (gene n) @ map ((#) (Neg (Suc n))) (gene n)"

value "gene 1"

text \<open>We generate the code of @{term do_all_cdcl\<^sub>W_stgy_nat} with a stringer type specification to
  avoid the explicit manipulation of a \<open>HOL.equal\<close> record.\<close>
definition do_all_cdcl\<^sub>W_stgy_nat :: "nat cdcl\<^sub>W_restart_state_inv_from_init_state
   \<Rightarrow> nat cdcl\<^sub>W_restart_state_inv_from_init_state" where
"do_all_cdcl\<^sub>W_stgy_nat = do_all_cdcl\<^sub>W_stgy"

definition init_state_init_state_of :: \<open>nat literal list list \<Rightarrow> _\<close> where
  \<open>init_state_init_state_of N = ConI ([], (map remdups N), [], None)\<close>

lemma [code abstract]:
  shows "rough_state_from_init_state_of (init_state_init_state_of N) = ([], map remdups N, [], None)"
proof -
  have 1: \<open>(init_state_init_state_of N) = state_from_init_state_of ([], map remdups N, [], None)\<close>
    by (auto simp: init_state_init_state_of_def ConI_def cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def
      distinct_mset_set_def
    intro!: state_of_inject[THEN iffD2])
  show ?thesis unfolding 1
    apply (subst state_from_init_state_of_inverse)
    by (auto simp: cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def
        distinct_mset_set_def)
qed

code_identifier
  code_module DPLL_CDCL_W_Implementation \<rightharpoonup> (OCaml) CDCL_W_Level

export_code do_all_cdcl\<^sub>W_stgy_nat Pos Neg natural_of_nat nat_of_integer init_state_init_state_of
  integer_of_int int_of_integer
  in SML
  module_name SAT_Solver
  file "code/functional_solver.sml"

end
