theory CDCL_Two_Watched_Literals_Simple_Implementation_List_List_Refinement
  imports CDCL_Two_Watched_Literals_Simple_Implementation_List_Refinement
begin

section \<open>Third Refinement: List of lists\<close>

subsection \<open>Types\<close>
type_synonym 'v working_queue_array = "(nat \<times> nat) multiset"
type_synonym 'v lit_queue_list = "'v literal list"

type_synonym 'v twl_st_ll =
  "('v, nat) ann_lits \<times> 'v literal list list \<times> nat \<times>
    'v clause_list option \<times> nat \<times> 'v working_queue_array \<times> 'v lit_queue"

fun get_clauses_ll :: "'v twl_st_ll \<Rightarrow> 'v literal list list" where
  \<open>get_clauses_ll (_, N, _, _, _, _, _) = N\<close>

fun working_queue_ll :: "'v twl_st_ll \<Rightarrow> (nat \<times> nat) multiset" where
  \<open>working_queue_ll (_, _, _, _, _, WS, _) = WS\<close>

fun set_working_queue_ll :: "(nat \<times> nat) multiset \<Rightarrow> 'v twl_st_ll \<Rightarrow>
  'v twl_st_ll" where
  \<open>set_working_queue_ll WS (M, N, U, D, NP, _, Q) = (M, N, U, D, NP, WS, Q)\<close>

fun pending_ll :: "'v twl_st_ll \<Rightarrow> 'v literal multiset" where
  \<open>pending_ll (_, _, _, _, _, _, Q) = Q\<close>

fun set_pending_ll :: "'v literal multiset \<Rightarrow> 'v twl_st_ll \<Rightarrow> 'v twl_st_ll" where
  \<open>set_pending_ll Q (M, N, U, D, NP, WS, _) = (M, N, U, D, NP, WS, Q)\<close>

fun get_conflict_ll :: "'v twl_st_ll \<Rightarrow> 'v literal list option" where
  \<open>get_conflict_ll (_, _, _, D, _, _, _) = D\<close>

fun twl_clause_of_ll :: \<open>'a list \<Rightarrow> 'a list twl_clause\<close> where
  \<open>twl_clause_of_ll (x # y # xs) = TWL_Clause [x, y] xs\<close>

fun convert_lit_ll :: \<open>'v literal list list \<Rightarrow> ('v, nat) ann_lit \<Rightarrow> ('v, 'v clause_list) ann_lit\<close> where
  \<open>convert_lit_ll _ (Decided K) = Decided K\<close>
| \<open>convert_lit_ll N (Propagated K i) = Propagated K (N!i)\<close>

abbreviation convert_lits_ll where
  \<open>convert_lits_ll N \<equiv> map (convert_lit_ll N)\<close>

fun twl_st_of_ll :: \<open>'v twl_st_ll  \<Rightarrow> 'v twl_st_list\<close> where
\<open>twl_st_of_ll S =
  (let (M, N, U, C, NP, WS, Q) = S;
        M' = convert_lits_ll N M;
        N' = twl_clause_of_ll `# mset (sublist N {0..< NP});
        U' = twl_clause_of_ll `# filter_mset (\<lambda>C. length C > 1) (mset (sublist N {U..< length N}));
        UP' = mset `# filter_mset (\<lambda>C. length C = 1) (mset (sublist N {U..< length N}));
        NP' = mset `# mset (sublist N {NP..< U});
        WS' = (\<lambda>(i, j). (i, twl_clause_of_ll (N!j))) `# WS
    in
  (M', N', U', C, NP', UP', WS', Q)
  )
\<close>

fun twl_clause_of_ll_inv where
  \<open>twl_clause_of_ll_inv (M, N, U, C, NP, WS, Q) \<longleftrightarrow>
    (\<forall>L i. Propagated L i \<in> set M \<longrightarrow> i < length N) \<and>
    (\<forall>(i, j) \<in># WS. (j < NP \<or> j \<ge> U) \<and> j < length N \<and> length (N!j) > 1) \<and>
    NP \<le> U \<and> U \<le> length N\<close>

lemma lit_of_convert_lit_ll[simp]: \<open>lit_of (convert_lit_ll S C) = lit_of C\<close>
  by (cases C) auto

lemma lits_of_convert_lit_ll[simp]: \<open>lits_of (convert_lit_ll S ` M) = lits_of M\<close>
  unfolding lits_of_def by (auto simp: image_image)

lemma defined_lit_convert_lits_ll[iff]: \<open>defined_lit (convert_lits_ll S M) L \<longleftrightarrow> defined_lit M L\<close>
  by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)

lemma valued_convert_lits_ll[simp]: \<open>valued (convert_lits_ll S M) L = valued M L\<close>
  unfolding valued_def by auto

fun list_swap where
  \<open>list_swap C i j = C [j := C ! i, i := C ! j]\<close>

definition update_clause_ll where
  \<open>update_clause_ll C i j = list_swap C i j\<close>

definition unwatched_ll where
\<open>unwatched_ll C = unwatched (twl_clause_of_ll C)\<close>

definition watched_ll where
\<open>watched_ll C = watched (twl_clause_of_ll C)\<close>

definition unit_propagation_inner_loop_body_ll :: "nat \<times> nat \<Rightarrow>
  'v twl_st_ll \<Rightarrow> 'v twl_st_ll nres"  where
  \<open>unit_propagation_inner_loop_body_ll C' S = do {
    let (M, N, U, D, NP, WS, Q) = S;
    let (i, j) = C';
    let L = (N ! j) ! i;
    let L' = (N ! j) ! (1 - i);
    ASSERT(L' \<in># mset (watched_ll (N ! j)) - {#L#});
    ASSERT (mset (watched_ll (N ! j)) = {#L, L'#});
    val_L' \<leftarrow> valued M L';
    ASSERT(val_L' = Some True \<longleftrightarrow> L' \<in> lits_of_l M);
    ASSERT(val_L' = Some False \<longleftrightarrow> -L' \<in> lits_of_l M);
    ASSERT(val_L' = None \<longleftrightarrow> undefined_lit M L');
    if val_L' = Some True
    then RETURN S
    else do {
      f \<leftarrow> find_unwatched M (unwatched_ll (N!j));
      ASSERT (fst f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched_ll (N!j)). - L \<in> lits_of_l M));
      if fst f = None
      then
        if val_L' = Some False
        then do {RETURN (M, N, U, Some (N ! j), NP, {#}, {#})}
        else do {RETURN (Propagated L' j # M, N, U, D, NP, WS, add_mset (-L') Q)}
      else do {
        let K = (N ! j) ! (snd f);
        RETURN (M, update_clause_ll N i (snd f), U, D, NP, WS, Q)
      }
    }
   }
\<close>

lemma in_set_sublist_uptI:
  assumes \<open>j \<ge> a\<close> and \<open>j < b\<close> and \<open>b \<le> length N\<close>
  shows \<open>(N ! j) \<in> set (sublist N {a..<b})\<close>
proof -
  have \<open>(N!j, j) \<in>{x \<in> set (zip N [0..<length N]). a \<le> snd x \<and> snd x < b}\<close>
    using assms by (auto simp: set_zip)
  then show ?thesis
    unfolding sublist_def by auto
qed

definition find_unwatched_ll where
\<open>find_unwatched_ll M C = do {
  WHILE\<^sub>T\<^bsup>\<lambda>(found, i). 2 \<le> i \<and> i \<le> length C \<and> (\<forall>j<i. 2 \<le> j \<longrightarrow> -(C!j) \<in> lits_of_l M) \<and>
    (found = Some False \<longrightarrow> (undefined_lit M (C!i) \<and> 2 \<le> i \<and> i < length C)) \<and>
    (found = Some True \<longrightarrow> (C!i \<in> lits_of_l M \<and>  2 \<le> i \<and> i < length C)) \<^esup>
    (\<lambda>(found, i). found = None \<and> i < length C)
    (\<lambda>(_, i). do {
      v \<leftarrow> valued M (C!i);
      case v of
        None \<Rightarrow> do { RETURN (Some False, i)}
      | Some True \<Rightarrow> do { RETURN (Some True, i)}
      | Some False \<Rightarrow> do { RETURN (None, i+1)}
      }
    )
    (None, 2::nat)
  }
\<close>

lemma length_sublist_upto: \<open>length (sublist l {a..<b}) = min (length l) b - a\<close>
proof -
  have \<open>card {i. i < length l \<and> a \<le> i \<and> i < b} = card {i. a \<le> i \<and> i < length l \<and> i < b}\<close>
    by meson
  also have \<open>\<dots> = card {i. a \<le> i \<and> i < min (length l) b}\<close>
    by auto
  also have \<open>\<dots> = card {a..<min (length l) b}\<close>
    by (rule arg_cong[of _ _ card]) auto
  finally show ?thesis by (auto simp: length_sublist)
qed

lemma nth_sublist_upto: \<open>j \<ge> a \<Longrightarrow> j \<le> b \<Longrightarrow> j \<le> length C \<Longrightarrow> sublist C {a..<b} ! j = C ! (j+a)\<close>
unfolding sublist_def
apply (subst nth_map)

apply (auto simp: nth_map)
sorry

lemma \<open>(find_unwatched_ll, find_unwatched) \<in> Id \<rightarrow> {(C', C). C' = unwatched_ll C \<and> length C' \<ge> 2} \<rightarrow> 
  \<langle>{((found', i'), (found, i)). found' = found \<and> i' = i + 2}\<rangle>nres_rel\<close>
unfolding find_unwatched_ll_def find_unwatched_def
apply (refine_rcg)
subgoal by auto
subgoal by auto
subgoal apply (auto simp: unwatched_ll_def length_sublist_upto)
sorry
subgoal
apply (auto simp: unwatched_ll_def )
oops

lemma unit_propagation_inner_loop_body_list:
  assumes
    WS: \<open>(i, j) \<in># working_queue_ll S\<close> and
    struct_invs: \<open>twl_struct_invs (twl_st_of (twl_st_of_ll S))\<close> and
    C_N_U: \<open>twl_clause_of C \<in># get_clauses (twl_st_of (twl_st_of_ll S))\<close> and
    add_inv: \<open>additional_WS_invs (twl_st_of_ll S)\<close> and
    stgy_inv: \<open>twl_stgy_invs (twl_st_of (twl_st_of_ll S))\<close> and
    inv_ll: \<open>twl_clause_of_ll_inv S\<close>
  shows
  \<open>unit_propagation_inner_loop_body_ll (i, j) (set_working_queue_ll (working_queue_ll S - {#(i, j)#}) S) \<le>
      \<Down> {(S, S'). S' = twl_st_of_ll S \<and> additional_WS_invs S' \<and> twl_stgy_invs (twl_st_of S') \<and> twl_struct_invs (twl_st_of S')}
      (unit_propagation_inner_loop_body_list (i, twl_clause_of_ll (get_clauses_ll S ! j))
      (set_working_queue_list (working_queue_list (twl_st_of_ll S) - {#(i, twl_clause_of_ll (get_clauses_ll S ! j))#}) (twl_st_of_ll S)))\<close>
proof -
  obtain M N U D NP WS Q where
    S: \<open>S = (M, N, U, D, NP, WS, Q)\<close>
    by (cases S) auto
  define M' N' U' UP' NP' WS' where
     \<open>M' \<equiv> convert_lits_ll N M\<close> and
     \<open>N' \<equiv> twl_clause_of_ll `# mset (sublist N {0..< NP})\<close> and
     \<open>U' \<equiv> twl_clause_of_ll `# filter_mset (\<lambda>C. length C > 1) (mset (sublist N {U..< length N}))\<close> and
     \<open>UP' \<equiv> mset `# filter_mset (\<lambda>C. length C = 1) (mset (sublist N {U..< length N}))\<close> and
     \<open>NP' \<equiv> mset `# mset (sublist N {NP..< U})\<close> and
     \<open>WS' = (\<lambda>(i, j). (i, twl_clause_of_ll (N!j))) `# WS\<close>
  have S': \<open>twl_st_of_ll S = (M', N', U', D, NP', UP', WS', Q)\<close>
    unfolding M'_def N'_def U'_def UP'_def NP'_def WS'_def S by auto
  have i: \<open>i = 0 \<or> i = 1\<close>
    using WS add_inv unfolding S by (auto simp: additional_WS_invs_def)
  have NP_U: \<open>NP \<le> U\<close> and U_N: \<open>U \<le> length N\<close>
    using inv_ll unfolding S by auto
  have dist_q: \<open>distinct_queued (twl_st_of (twl_st_of_ll S))\<close>
    using struct_invs unfolding twl_struct_invs_def by fast
  have \<open>(i, twl_clause_of_ll (N!j)) \<in># WS'\<close>
    using WS unfolding WS'_def S by auto

  have \<open>(j < NP \<or> U \<le> j) \<and> j < length N\<close> and N_j_1: \<open>length (N!j) > 1\<close>
    using inv_ll WS unfolding S N'_def U'_def by auto
  then have \<open>twl_clause_of_ll (N!j) \<in># N' + U'\<close>
    using NP_U U_N unfolding S N'_def U'_def by (auto simp: in_set_sublist_uptI)

  obtain L L' UW where N_j: \<open>N!j = [L, L'] @ UW\<close>
    using N_j_1 by (metis One_nat_def add.left_neutral append_Cons append_Nil less_irrefl list.size(3)
        list.size(4) neq_Nil_conv not_less_zero)
  have [simp]: \<open>watched_ll (L # L' # UW) = [L, L']\<close> and
    [simp]: \<open>twl_clause_of_ll (N ! j) = TWL_Clause [L, L'] UW\<close>
    by (auto simp: watched_ll_def N_j)
  have valued_refinement:
    \<open>valued M1 (N' ! j' ! (1 - i')) \<le> \<Down> Id (valued M2 (watched C' ! (1 - i'')))\<close>
    if \<open>M2 = convert_lits_ll N M1\<close> and \<open>M1 = M\<close> and \<open>N' = N\<close> and \<open>j' = j\<close> and \<open>j'' = j\<close> and
    \<open>C' = twl_clause_of_ll (N' ! j'')\<close> and \<open>i' = i\<close> and \<open>i'' = i\<close>
    for M1 :: \<open>('a, nat) ann_lits\<close> and M2 :: \<open>('a, 'a literal list) ann_lit list\<close> and N' and
    j' j'' i' i'' :: nat and C'
    using that i N_j S by auto
  have remove_S_ll: \<open>set_working_queue_ll (remove1_mset (i, j) (working_queue_ll (M, N, U, D, NP, WS, Q)))
            (M, N, U, D, NP, WS, Q) = (M, N, U, D, NP, remove1_mset (i, j) WS, Q)\<close>
  by simp
  have remove_S: \<open>set_working_queue_list
        (remove1_mset (i, twl_clause_of_ll (N ! j))
          (working_queue_list
            (twl_st_of_ll (M, N, U, D, NP, WS, Q))))
        (twl_st_of_ll (M, N, U, D, NP, WS, Q)) =
       (M', N', U', D, NP', UP', remove1_mset (i, TWL_Clause [L, L'] UW) WS', Q)\<close>
  by (simp add: M'_def N'_def U'_def S NP'_def UP'_def WS'_def)

  show ?thesis
    unfolding unit_propagation_inner_loop_body_ll_def unit_propagation_inner_loop_body_list_def
      S remove_S remove_S_ll
using [[goals_limit=22]]
    apply (refine_vcg valued_refinement(* ; remove_dummy_vars simp: remove_S_ll *))
oops
    subgoal using N_j i remove_S by auto
    subgoal using N_j i by auto
    subgoal using N_j i unfolding S by auto
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal by (auto simp:)
    subgoal sorry
    subgoal using N_j i apply (auto simp add: image_mset_remove1_mset_if) oops by auto

    subgoal using N_j i by auto
    subgoal
oops

end