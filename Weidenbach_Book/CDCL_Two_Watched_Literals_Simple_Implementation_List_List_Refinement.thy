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

definition clause_nth :: \<open>'v twl_st_ll \<Rightarrow> nat \<Rightarrow> 'v literal list\<close> where
  \<open>clause_nth = (\<lambda>(M, CS, U, D, NP, WS, Q) j. CS ! j)\<close>

fun twl_clause_of_ll :: \<open>'a list \<Rightarrow> 'a list twl_clause\<close> where
  \<open>twl_clause_of_ll (x # y # xs) = TWL_Clause [x, y] xs\<close>

fun convert_lit_ll :: \<open>'v twl_st_ll \<Rightarrow> ('v, nat) ann_lit \<Rightarrow> ('v, 'v clause_list) ann_lit\<close> where
  \<open>convert_lit_ll _ (Decided K) = Decided K\<close>
| \<open>convert_lit_ll S (Propagated K i) = Propagated K (clause_nth S i)\<close>

abbreviation convert_lits_ll where
  \<open>convert_lits_ll S \<equiv> map (convert_lit_ll S)\<close>

fun twl_st_of_ll :: \<open>'v twl_st_ll  \<Rightarrow> 'v twl_st_list\<close> where
\<open>twl_st_of_ll S =
  (let (M, N, U, C, NP, WS, Q) = S;
        M' = convert_lits_ll S M;
        N' = twl_clause_of_ll `# mset (sublist N {0..< NP});
        U' = twl_clause_of_ll `# filter_mset (\<lambda>C. length C > 1) (mset (sublist N {U..< length N}));
        UP' = mset `# filter_mset (\<lambda>C. length C = 1) (mset (sublist N {U..< length N}));
        NP' = mset `# mset (sublist N {NP..< U})
    in
  (M', N', U', C, NP', UP', (\<lambda>(i, j). (i, twl_clause_of_ll (clause_nth S j))) `# WS, Q)
  )
\<close>

fun twl_clause_of_ll_inv where
  \<open>twl_clause_of_ll_inv (M, N, U, C, NP, WS, Q) \<longleftrightarrow>
    (\<forall>L i. Propagated L i \<in> set M \<longrightarrow> i < length N) \<and>
    NP < U \<and> U < length N\<close>

fun list_swap where
  \<open>list_swap C i j = C [j := C ! i, i := C ! j]\<close>

definition update_clause_ll where
  \<open>update_clause_ll C i j = list_swap C i j\<close>

definition unit_propagation_inner_loop_body_ll :: "nat \<times> nat \<Rightarrow>
  'v twl_st_ll \<Rightarrow> 'v twl_st_ll nres"  where
  \<open>unit_propagation_inner_loop_body_ll C' S = do {
    let (M, N, U, D, NP, WS, Q) = S;
    let (i, j) = C';
    let L = (N ! j) ! i;
    let L' = (N ! j) ! (1 - i);
    ASSERT(L' \<in># {#(N ! j)!0, (N ! j)!1#} - {#L#});
    ASSERT ({#(N ! j)!0, (N ! j)!1#} = {#L, L'#});
    val_L' \<leftarrow> valued M L';
    ASSERT(val_L' = Some True \<longleftrightarrow> L' \<in> lits_of_l M);
    ASSERT(val_L' = Some False \<longleftrightarrow> -L' \<in> lits_of_l M);
    ASSERT(val_L' = None \<longleftrightarrow> undefined_lit M L');
    if val_L' = Some True
    then RETURN S
    else do {
      f \<leftarrow> find_unwatched M (sublist (N ! j) {2..<length (N ! j)});
      ASSERT (fst f = None \<longleftrightarrow> (\<forall>L\<in>#mset (sublist (N ! j) {2..<length (N ! j)}). - L \<in> lits_of_l M));
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

lemma unit_propagation_inner_loop_body_list:
  assumes
      WS: \<open>(i, j) \<in># working_queue_ll S\<close> and
      i: \<open>i = 0 \<or> i = 1\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of (twl_st_of_ll S))\<close> and
      C_N_U: \<open>twl_clause_of C \<in># get_clauses (twl_st_of (twl_st_of_ll S))\<close> and
      add_inv: \<open>additional_WS_invs (twl_st_of_ll S)\<close> and
      stgy_inv: \<open>twl_stgy_invs (twl_st_of (twl_st_of_ll S))\<close>
  shows
  \<open>unit_propagation_inner_loop_body_ll (i, j) (set_working_queue_ll (working_queue_ll S - {#(i, j)#}) S) \<le>
      \<Down> {(S, S'). S' = twl_st_of_ll S \<and> additional_WS_invs S' \<and> twl_stgy_invs (twl_st_of S') \<and> twl_struct_invs (twl_st_of S')} 
      (unit_propagation_inner_loop_body_list (i, twl_clause_of_ll (clause_nth S j)) 
      (set_working_queue_list (working_queue_list (twl_st_of_ll S) - {#(i, twl_clause_of_ll (clause_nth S j))#}) (twl_st_of_ll S)))\<close>
  unfolding unit_propagation_inner_loop_body_ll_def unit_propagation_inner_loop_body_list_def 
  apply (refine_vcg bind_refine_spec[where M' = \<open>find_unwatched _ _\<close>, OF _ find_unwatched]
        bind_refine_spec[where M' = \<open>valued _ _\<close>, OF _ valued_spec] 
        update_clauses_list_spec
        case_prod_bind[of _ \<open>If _ _\<close>]; remove_dummy_vars)

     prefer 3
thm case_prod_bind[of _ \<open>If _ _\<close>]
     apply refine_rcg

end