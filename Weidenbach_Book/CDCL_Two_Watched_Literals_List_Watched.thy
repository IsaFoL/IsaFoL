theory CDCL_Two_Watched_Literals_List_Watched
  imports CDCL_Two_Watched_Literals_List
begin

section \<open>Third Refinement: Remembering watched\<close>

subsection \<open>Types\<close>
typ working_queue_l

type_synonym working_queue_wl = "nat multiset"

type_synonym 'v twl_st_wl =
  "('v, nat) ann_lits \<times> 'v clause_l list \<times> nat \<times>
    'v clause_l option \<times> 'v clauses \<times> 'v clauses \<times> working_queue_wl \<times> 'v lit_queue \<times>
    ('v literal \<Rightarrow> nat multiset)"


fun working_queue_wl :: "'v twl_st_wl \<Rightarrow> working_queue_wl" where
  \<open>working_queue_wl (_, _, _, _, _, _, WS, _) = WS\<close>

fun get_trail_wl :: "'v twl_st_wl \<Rightarrow> ('v, nat) ann_lit list" where
  \<open>get_trail_wl (M, _, _, _, _, _, _, _) = M\<close>

fun set_working_queue_wl :: "working_queue_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl" where
  \<open>set_working_queue_wl WS (M, N, U, D, NP, UP, _, Q) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun pending_wl :: "'v twl_st_l \<Rightarrow> 'v literal multiset" where
  \<open>pending_wl (_, _, _, _, _, _, _, Q) = Q\<close>

fun set_pending_wl :: "'v literal multiset \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l" where
  \<open>set_pending_wl Q (M, N, U, D, NP, UP, WS, _) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun get_conflict_wl :: "'v twl_st_wl \<Rightarrow> 'v clause_l option" where
  \<open>get_conflict_wl (_, _, _, D, _, _, _, _) = D\<close>

fun correct_watching :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching (M, N, U, D, NP, UP, WS, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># \<Union>#(mset `# mset N). W L = clause_to_update L (M, N, U, D, NP, UP, {#}, Q))\<close>
  
fun watched_by where
  \<open>watched_by (M, N, U, D, NP, UP, WS, Q, W) L = W L\<close>

definition unit_propagation_inner_loop_body_wl :: "nat \<times> nat \<Rightarrow>
  'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres"  where
  \<open>unit_propagation_inner_loop_body_wl C' S = do {
    let (M, N, U, D, NP, UP, WS, Q, W) = S;
    let (i, C::nat) = C';
    let L = (watched_l (N!C)) ! i;
    let L' = (watched_l (N!C)) ! (1 - i);
    ASSERT(L' \<in># mset (watched_l (N!C)) - {#L#});
    ASSERT (mset (watched_l (N!C)) = {#L, L'#});
    val_L' \<leftarrow> valued M L';
    if val_L' = Some True
    then RETURN S
    else do {
      f \<leftarrow> find_unwatched M (N!C);
      ASSERT (fst f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched_l (N!C)). - L \<in> lits_of_l M));
      if fst f = None
      then
        if val_L' = Some False
        then do {RETURN (M, N, U, Some (N!C), NP, UP, {#}, {#}, W)}
        else do {RETURN (Propagated L' C # M, N, U, D, NP, UP, WS, add_mset (-L') Q, W)}
      else do {
        let K = (N!C) ! (snd f);
        let N' = list_update N C (swap (N!C) i (snd f));
        RETURN (M, N', U, D, NP, UP, WS, Q, W)
      }
    }
   }
\<close>

fun st_l_of_wl :: \<open>'v twl_st_wl  \<Rightarrow> 'v twl_st_l\<close> where
  \<open>st_l_of_wl (M, N, C, D, NP, UP, WS, Q, W) = (M, N, C, D, NP, UP, WS, Q)\<close>

fun twl_st_of_l :: \<open>'v literal option \<Rightarrow> 'v twl_st_wl  \<Rightarrow> 'v twl_st\<close> where
  \<open>twl_st_of_l L S = twl_st_of L (st_l_of_wl S)\<close>

definition unit_propagation_outer_loop_wl :: "'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres"  where
  \<open>unit_propagation_outer_loop_wl S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_struct_invs (twl_st_of_l S) \<and> twl_stgy_invs (twl_st_of_l S) \<and>
      working_queue_wl S = {#}\<^esup>
      (\<lambda>S. pending_wl S \<noteq> {#})
      (\<lambda>S. do {
        L \<leftarrow> SPEC (\<lambda>L. L \<in># pending_wl S);
        let S' = set_working_queue_wl (watched_by S L)
           (set_pending_l (pending_wl S - {#L#}) S);
        unit_propagation_inner_loop_wl L S'
      })
      S\<^sub>0
\<close>
 
end
