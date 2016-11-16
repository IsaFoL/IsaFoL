theory CDCL_Two_Watched_Literals_List_Watched
  imports CDCL_Two_Watched_Literals_List
begin

section \<open>Third Refinement: Remembering watched\<close>

subsection \<open>Types\<close>

type_synonym working_queue_wl = "nat multiset"
type_synonym watched = "nat multiset"
type_synonym 'v lit_queue_wl = "'v literal multiset"

type_synonym 'v twl_st_wl =
  "('v, nat) ann_lits \<times> 'v clause_l list \<times> nat \<times>
    'v clause_l option \<times> 'v clauses \<times> 'v clauses \<times> working_queue_wl \<times> 'v lit_queue_wl \<times>
    ('v literal \<Rightarrow> watched)"


fun working_queue_wl :: "'v twl_st_wl \<Rightarrow> working_queue_wl" where
  \<open>working_queue_wl (_, _, _, _, _, _, WS, _) = WS\<close>

fun get_trail_wl :: "'v twl_st_wl \<Rightarrow> ('v, nat) ann_lit list" where
  \<open>get_trail_wl (M, _, _, _, _, _, _, _) = M\<close>

fun set_working_queue_wl :: "working_queue_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl" where
  \<open>set_working_queue_wl WS (M, N, U, D, NP, UP, _, Q) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun pending_wl :: "'v twl_st_wl \<Rightarrow> 'v lit_queue_wl" where
  \<open>pending_wl (_, _, _, _, _, _, _, Q, _) = Q\<close>

fun set_pending_wl :: "'v lit_queue_wl \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl" where
  \<open>set_pending_wl Q (M, N, U, D, NP, UP, WS, _, W) = (M, N, U, D, NP, UP, WS, Q, W)\<close>

fun get_conflict_wl :: "'v twl_st_wl \<Rightarrow> 'v clause_l option" where
  \<open>get_conflict_wl (_, _, _, D, _, _, _, _) = D\<close>

fun correct_watching :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching (M, N, U, D, NP, UP, WS, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># \<Union>#(mset `# mset N). W L = clause_to_update L (M, N, U, D, NP, UP, {#}, {#}))\<close>

fun correct_watching_except :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> bool\<close> where
  \<open>correct_watching_except (M, N, U, D, NP, UP, WS, Q, W) L \<longleftrightarrow>
    (\<forall>L \<in> (\<Union>(set ` set N)) - {L}. W L = clause_to_update L (M, N, U, D, NP, UP, {#}, {#}))\<close>

fun watched_by :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> watched\<close> where
  \<open>watched_by (M, N, U, D, NP, UP, WS, Q, W) L = W L\<close>

fun update_watched :: \<open>'v literal \<Rightarrow> watched \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>update_watched L WL (M, N, U, D, NP, UP, WS, Q, W) = (M, N, U, D, NP, UP, WS, Q, W(L:= WL))\<close>

text \<open>We here also update the list of watched clauses \<^term>\<open>WL\<close>. It would be more memory efficient
  to directly iterate over \<^term>\<open>W L\<close>, but this is not compatible with multisets.\<close>
definition unit_propagation_inner_loop_body_wl :: "'v literal \<Rightarrow> nat \<Rightarrow> watched \<Rightarrow>
  'v twl_st_wl \<Rightarrow> (watched \<times> 'v twl_st_wl) nres"  where
  \<open>unit_propagation_inner_loop_body_wl L C WL S = do {
    let (M, N, U, D, NP, UP, WS, Q, W) = S;
    let i = (if (watched_l (N!C)) ! 0 = L then 0 else 1);
    let L = (watched_l (N!C)) ! i;
    let L' = (watched_l (N!C)) ! (1 - i);
    ASSERT(L' \<in># mset (watched_l (N!C)) - {#L#});
    ASSERT (mset (watched_l (N!C)) = {#L, L'#});
    val_L' \<leftarrow> valued M L';
    if val_L' = Some True
    then RETURN (WL, S)
    else do {
      f \<leftarrow> find_unwatched M (N!C);
      ASSERT (fst f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched_l (N!C)). - L \<in> lits_of_l M));
      if fst f = None
      then
        if val_L' = Some False
        then do {RETURN (add_mset C WL, (M, N, U, Some (N!C), NP, UP, {#}, {#}, W))}
        else do {RETURN (add_mset C WL, (Propagated L' C # M, N, U, D, NP, UP, WS, add_mset (-L') Q, W))}
      else do {
        let K = (N!C) ! (snd f);
        let N' = list_update N C (swap (N!C) i (snd f));
        RETURN (WL, (M, N', U, D, NP, UP, WS, Q, W(L := remove1_mset C (W L), K:= add_mset C (W K))))
      }
    }
   }
\<close>

fun st_l_of_wl :: \<open>'v twl_st_wl  \<Rightarrow> 'v twl_st_l\<close> where
  \<open>st_l_of_wl (M, N, C, D, NP, UP, WS, Q, W) = (M, N, C, D, NP, UP, WS, Q)\<close>

fun twl_st_of_wl :: \<open>'v literal option \<Rightarrow> 'v twl_st_wl  \<Rightarrow> 'v twl_st\<close> where
  \<open>twl_st_of_wl L S = twl_st_of L (st_l_of_wl S)\<close>

definition unit_propagation_inner_loop_wl :: "'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres" where
  \<open>unit_propagation_inner_loop_wl L S\<^sub>0 = do {
    (WL, S) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(WL, S). twl_struct_invs (twl_st_of_wl (Some L) S) \<and> twl_stgy_invs (twl_st_of_wl (Some L) S) \<and>
    cdcl_twl_cp\<^sup>*\<^sup>* (twl_st_of_wl (Some L) S\<^sub>0) (twl_st_of_wl (Some L) S)\<^esup>
      (\<lambda>(WL, S). working_queue_wl S \<noteq> {#})
      (\<lambda>(WL, S). do {
        C \<leftarrow> SPEC (\<lambda>C. C \<in># working_queue_wl S);
        let S' = set_working_queue_wl (working_queue_wl S - {#C#}) S;
        unit_propagation_inner_loop_body_wl L C WL S'
      })
      ({#}, S\<^sub>0);
      RETURN (update_watched L WL S)
  }
  \<close>

lemma working_queue_l_working_queue_wl: \<open>working_queue_l (st_l_of_wl S) = working_queue_wl S\<close>
  by (cases S) auto

lemma
  assumes \<open>correct_watching S\<close>
  shows \<open>(uncurry unit_propagation_inner_loop_wl, uncurry unit_propagation_inner_loop_l) \<in>
    {((L', T'::'v twl_st_wl), (L, T::'v twl_st_l)). L = L' \<and> st_l_of_wl T' = T} \<rightarrow> \<langle>{(T', T). st_l_of_wl T' = T}\<rangle>nres_rel
    \<close> (is \<open>?fg \<in> ?A \<rightarrow> \<langle>?B\<rangle>nres_rel\<close>)
  unfolding unit_propagation_inner_loop_wl_def unit_propagation_inner_loop_l_def uncurry_def
  apply (subst (10) nres_monad2[symmetric, of])
  apply clarify
  apply (refine_vcg WHILEIT_refine[where R = \<open>{((WT'::watched, T'::'v twl_st_wl), T). st_l_of_wl T' = T}\<close>] )
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp add: working_queue_l_working_queue_wl)
  subgoal by (auto simp add: working_queue_l_working_queue_wl)
  subgoal by (auto simp add: working_queue_l_working_queue_wl)
  subgoal by auto
oops  
  
definition unit_propagation_outer_loop_wl :: "'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres"  where
  \<open>unit_propagation_outer_loop_wl S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and> twl_stgy_invs (twl_st_of_wl None S) \<and>
      working_queue_wl S = {#}\<^esup>
      (\<lambda>S. pending_wl S \<noteq> {#})
      (\<lambda>S. do {
        L \<leftarrow> SPEC (\<lambda>L. L \<in># pending_wl S);
        let S' = set_working_queue_wl (watched_by S L) (set_pending_wl (remove1_mset L (pending_wl S)) S);
        unit_propagation_inner_loop_wl L S'
      })
      S\<^sub>0
\<close>

end
