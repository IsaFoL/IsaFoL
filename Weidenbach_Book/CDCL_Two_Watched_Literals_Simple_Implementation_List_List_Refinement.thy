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

(* TODO: we do not need to convert to multiset: we cannot update a clause that has been put
  on the trail.
  And ensuring that the true literal is at position 0 might be useful\<dots>*)
fun convert_lit_ll :: \<open>'v literal list list \<Rightarrow> ('v, nat) ann_lit \<Rightarrow> ('v, 'v clause_list) ann_lit\<close> where
  \<open>convert_lit_ll _ (Decided K) = Decided K\<close>
| \<open>convert_lit_ll N (Propagated K i) = Propagated K ((N!i))\<close>

abbreviation convert_lits_ll_m where
  \<open>convert_lits_ll_m  N \<equiv> map (convert_lit_ll N)\<close>

fun take_between :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  \<open>take_between i j l = take (j - i) (drop i l)\<close>

text \<open>The two states are related if... TODO.\<close>
definition twl_st_of_ll :: \<open>('v twl_st_ll \<times> 'v twl_st_list) set\<close> where
\<open>twl_st_of_ll = {(S', S).
  (let (M, N, U, C, NP, WS, Q) = S';
       (M', N', U', C', NP', UP', WS', Q') = S;
        SM' = convert_lits_ll_m  N M;
        SN' = twl_clause_of_ll `# mset (take NP N);
        SU' = twl_clause_of_ll `# filter_mset (\<lambda>C. length C > 1) (mset (drop U N));
        SUP' = mset `# filter_mset (\<lambda>C. length C = 1) (mset (drop U N));
        SNP' = mset `# mset (take_between NP U N);
        SWS' = (\<lambda>(i, j). (i, twl_clause_of_ll (N!j))) `# WS;
        SC = map_option mset C;
        S'C' = map_option mset C'
    in
  (SM', SN', SU', SC, SNP', SUP', SWS', Q) = (M', N', U', S'C', NP', UP', WS', Q'))}
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

lemma defined_lit_convert_lits_ll_m [iff]: \<open>defined_lit (convert_lits_ll_m  S M) L \<longleftrightarrow> defined_lit M L\<close>
  by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)

lemma valued_convert_lits_ll_m [simp]: \<open>valued (convert_lits_ll_m  S M) L = valued M L\<close>
  unfolding valued_def by auto

fun list_swap where
  \<open>list_swap C i j = C [j := C ! i, i := C ! j]\<close>

definition update_clause_ll where
  \<open>update_clause_ll C i j = list_swap C i j\<close>

definition unwatched_ll where
\<open>unwatched_ll C = unwatched (twl_clause_of_ll C)\<close>

definition watched_ll where
\<open>watched_ll C = watched (twl_clause_of_ll C)\<close>

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


context
begin

private lemma set_Suc_less_upt: \<open>a \<le> b \<Longrightarrow> {j. a \<le> Suc j \<and> Suc j < b} = {a-1..<b-1}\<close>
  by auto

lemma nth_sublist_upto: \<open>a < length C \<Longrightarrow>  j < b - a \<Longrightarrow> j < length C - a \<Longrightarrow> sublist C {a..<b} ! j = C ! (j+a)\<close>
  by (induction C arbitrary: a b j)
    (auto simp: sublist_Cons nth_Cons set_Suc_less_upt split: nat.splits)

end

lemma list_length_ge_2_exists:
  \<open>length C \<ge> 2 \<longleftrightarrow> (\<exists>x y UW. C = x # y # UW)\<close>
  by (cases C; cases \<open>tl C\<close>)  auto

(* lemma convert_lits_l_m_convert_lits_ll_m_lits_of:
  \<open>convert_lits_l_m M' = convert_lits_ll_m N M \<Longrightarrow> lits_of_l M = lits_of_l M'\<close>
  apply (induction M' arbitrary: M rule: ann_lit_list_induct)
  subgoal by auto
  subgoal for L C M by (cases M; cases \<open>hd M\<close>; auto)
  subgoal for L C _ M by (cases M; cases \<open>hd M\<close>; auto)
  done *)

lemma find_unwatched_ll_spec:
  \<open>(find_unwatched_ll, find_unwatched) \<in> {(M', M). M = convert_lits_ll_m  N M'} \<rightarrow>
    {(C', C). C = unwatched_ll C' \<and> length C' \<ge> 2} \<rightarrow>
    \<langle>{((found', i'), (found, i)). i' = i + 2 \<and> found' = found}\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow> _ \<rightarrow> _\<close>)
proof -
(*   note convert_lits_l_m_convert_lits_ll_m_lits_of[simp]
  note Decided_Propagated_in_iff_in_lits_of_l[simp] *)
  have val: \<open>valued M' L \<le> \<Down> Id (valued M L')\<close>
    if \<open>(M', M) \<in> ?R\<close> and \<open>L = L'\<close> for M :: \<open>('a, 'a literal list) ann_lits\<close> and
    M' :: \<open>('a, nat) ann_lits\<close> and L L'
    using that by (auto simp: valued_def)
  show ?thesis
    unfolding find_unwatched_ll_def find_unwatched_def
    apply (refine_rcg val)
    subgoal by auto
    subgoal by auto
    subgoal for M M' C' C fi' fi
      by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    done
qed


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
      f \<leftarrow> find_unwatched_ll M (N!j);
      ASSERT (fst f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched_ll (N!j)). - L \<in> lits_of_l M));
      if fst f = None
      then
        if val_L' = Some False
        then do {RETURN (M, N, U, Some (N ! j), NP, {#}, {#})}
        else do {RETURN (Propagated L' j # M, N, U, D, NP, WS, add_mset (-L') Q)}
      else do {
        let K = (N ! j) ! (snd f) in
        let (N', U') = (N[j := update_clause_ll (N!j) i (snd f)], U) in
        RETURN (M, N', U', D, NP, WS, Q)
      }
    }
   }
\<close>
lemma refine_pair_to_SPEC_rev_eq:
  fixes g :: \<open>'s \<Rightarrow> ('c \<times> 's) nres\<close> and f :: \<open>'b \<Rightarrow> ('c \<times> 'b) nres\<close>
  assumes \<open>(f, g) \<in> {(S', S). S' = h S \<and> R S'} \<rightarrow> \<langle>{((brk', S'), (brk, S)). S' = h S \<and> brk = brk' \<and> P' S}\<rangle>nres_rel\<close>
    (is \<open>_ \<in> ?R \<rightarrow> ?I\<close>)
  assumes \<open>R S\<close> and [simp]: \<open>S = h S'\<close>
  shows \<open>f S \<le> \<Down> {((brk', S'), (brk, S)). S' = h S \<and> brk = brk' \<and> P' S} (g S')\<close>
proof -
  have \<open>(f S, g S') \<in> ?I\<close>
    using assms unfolding fun_rel_def by auto
  then show ?thesis
    unfolding nres_rel_def fun_rel_def  pw_le_iff pw_conc_inres pw_conc_nofail
    by auto
qed

lemma refine_pair_to_SPEC_rev_eq':
  fixes f :: \<open>'a \<Rightarrow> 's \<Rightarrow> ('c \<times> 't) nres\<close> and g :: \<open>'b \<Rightarrow> 's' \<Rightarrow> ('c \<times> 't) nres\<close>
  assumes \<open>(f, g) \<in> U \<rightarrow> {(S', S). h' S = h S' \<and> R S'} \<rightarrow>
    \<langle>{((brk', S'), (brk, S)). S' = h'' S \<and> brk' = brk}\<rangle>nres_rel\<close>
    (is \<open>_ \<in> _ \<rightarrow> ?R \<rightarrow> ?I\<close>)
  assumes \<open>R S\<close> and \<open>h' S' = h S\<close> \<open>(a, b) \<in> U\<close>
  shows \<open>f a S \<le> \<Down> {((brk', S'), (brk, S)). S' = h'' S \<and> brk' = brk} (g b S')\<close>
proof -
  have \<open>(f a S, g b S') \<in> ?I\<close>
    using assms unfolding fun_rel_def by auto
  then show ?thesis
    unfolding nres_rel_def fun_rel_def  pw_le_iff pw_conc_inres pw_conc_nofail
    by auto
qed
thm find_unwatched_ll_spec refine_pair_to_SPEC_rev_eq'
thm  find_unwatched_ll_spec[THEN refine_pair_to_SPEC_rev_eq']


lemma unit_propagation_inner_loop_body_list:
  assumes
    WS: \<open>(i, j) \<in># working_queue_ll S\<close> and
    struct_invs: \<open>twl_struct_invs (twl_st_of S')\<close> and
    SS': \<open>(S, S') \<in> twl_st_of_ll\<close> and
    C_N_U: \<open>twl_clause_of C \<in># get_clauses (twl_st_of S')\<close> and
    add_inv: \<open>additional_WS_invs S'\<close> and
    stgy_inv: \<open>twl_stgy_invs (twl_st_of S')\<close> and
    inv_ll: \<open>twl_clause_of_ll_inv S\<close>
  shows
  \<open>(unit_propagation_inner_loop_body_ll (i, j) (set_working_queue_ll (working_queue_ll S - {#(i, j)#}) S),
    unit_propagation_inner_loop_body_list (i, twl_clause_of_ll (get_clauses_ll S ! j))
      (set_working_queue_list (working_queue_list S' - {#(i, twl_clause_of_ll (get_clauses_ll S ! j))#}) S')
    ) \<in>
    \<langle>{(S, S'). (S, S') \<in> twl_st_of_ll \<and> twl_clause_of_ll_inv S \<and> additional_WS_invs S' \<and>
    twl_stgy_invs (twl_st_of S') \<and>
      twl_struct_invs (twl_st_of S')}\<rangle> nres_rel\<close>
    (is \<open>?C \<in> _\<close>)
proof -
  obtain M N U D NP WS Q where
    S: \<open>S = (M, N, U, D, NP, WS, Q)\<close>
    by (cases S) auto
  obtain S'M S'N S'U S'D S'NP S'UP S'WS S'Q where
    S': \<open>S' = (S'M, S'N, S'U, S'D, S'NP, S'UP, S'WS, S'Q)\<close>
    by (cases S') auto
  define M' N' U' UP' NP' WS' where
     \<open>M' = convert_lits_ll_m  N M\<close> and
     \<open>N' = twl_clause_of_ll `# mset (take NP N)\<close> and
     \<open>U' = twl_clause_of_ll `# filter_mset (\<lambda>C. length C > 1) (mset (drop U N))\<close> and
     \<open>UP' = mset `# filter_mset (\<lambda>C. length C = 1) (mset (drop U N))\<close> and
     \<open>NP' = mset `# mset (take_between NP U N )\<close> and
     \<open>WS' = (\<lambda>(i, j). (i, twl_clause_of_ll (N!j))) `# WS\<close>

  obtain S'M S'D where
    S': \<open>S' = (S'M, N', U', S'D, NP', UP', WS', Q)\<close> and
    S'D: \<open>map_option mset S'D = map_option mset D\<close> and
    S'M: \<open>S'M = convert_lits_ll_m  N M\<close>
    using SS' by (auto simp: twl_st_of_ll_def S S' N'_def U'_def UP'_def NP'_def WS'_def)

  have i: \<open>i = 0 \<or> i = 1\<close>
    using WS add_inv SS' unfolding S by (auto simp: additional_WS_invs_def twl_st_of_ll_def)
  have NP_U: \<open>NP \<le> U\<close> and U_N: \<open>U \<le> length N\<close>
    using inv_ll unfolding S by auto
  have dist_q: \<open>distinct_queued (twl_st_of S')\<close>
    using struct_invs unfolding twl_struct_invs_def by fast
  have \<open>(i, twl_clause_of_ll (N!j)) \<in># WS'\<close>
    using WS unfolding WS'_def S by auto
  have N_j_in_NP: \<open>N ! j \<in> set (take NP N)\<close> if \<open>j < NP\<close>
    using that by (metis NP_U U_N in_set_conv_nth length_take linear min_less_iff_conj nat_less_le nth_take)
  have j: \<open>(j < NP \<or> U \<le> j)\<close>\<open>j < length N\<close> and N_j_1: \<open>length (N!j) > 1\<close>
    using inv_ll WS unfolding S N'_def U'_def by auto
  then have \<open>twl_clause_of_ll (N!j) \<in># N' + U'\<close>
    using NP_U U_N unfolding S N'_def U'_def
    by (auto simp: in_set_drop_conv_nth intro!: imageI dest: N_j_in_NP)

  obtain L L' UW where N_j: \<open>N!j = [L, L'] @ UW\<close>
    using N_j_1 by (metis One_nat_def add.left_neutral append_Cons append_Nil less_irrefl list.size(3)
        list.size(4) neq_Nil_conv not_less_zero)
  have N_j_0: \<open>N ! j ! 0 = L\<close> and N_j_Suc_0: \<open>N ! j ! Suc 0 = L'\<close>
    unfolding N_j by auto
  have [simp]: \<open>watched_ll (L # L' # UW) = [L, L']\<close> and
    [simp]: \<open>twl_clause_of_ll (N ! j) = TWL_Clause [L, L'] UW\<close> and
    [simp]: \<open>unwatched_ll (L # L' # UW) = UW\<close> and
    [simp]: \<open>unwatched_ll (N ! j) = UW\<close>
    by (auto simp: watched_ll_def N_j unwatched_ll_def)
  have valued_refinement:
    \<open>valued M1 (N' ! j' ! (1 - i')) \<le> \<Down> Id (valued M2 (watched C' ! (1 - i'')))\<close>
    if \<open>M2 = convert_lits_ll_m  N M1\<close> and \<open>M1 = M\<close> and \<open>N' = N\<close> and \<open>j' = j\<close> and \<open>j'' = j\<close> and
    \<open>C' = twl_clause_of_ll (N' ! j'')\<close> and \<open>i' = i\<close> and \<open>i'' = i\<close>
    for M1 :: \<open>('a, nat) ann_lits\<close> and M2 :: \<open>('a, 'a literal list) ann_lit list\<close> and N' and
    j' j'' i' i'' :: nat and C'
    using that i N_j S by (auto simp: valued_def)
  have remove_S_ll: \<open>set_working_queue_ll (remove1_mset (i, j) (working_queue_ll (M, N, U, D, NP, WS, Q)))
            (M, N, U, D, NP, WS, Q) = (M, N, U, D, NP, remove1_mset (i, j) WS, Q)\<close>
    by simp
  have nth_UW_N: \<open>UW ! k = (N!j) ! (k+2)\<close> for k
    using N_j by auto
  have N_j_upd_0: \<open>(N ! j)[k := N ! j ! 0, 0 := N ! j ! k] = [N ! j ! k, N ! j ! 1] @ (drop 2 ((N ! j)[k := N ! j ! 0]))\<close>
    if \<open>k \<ge> 2\<close> for k
    using that N_j by (cases k; cases \<open>k-1\<close>) auto
  have remove_S:
    \<open>set_working_queue_list
      (remove1_mset (i, twl_clause_of_ll (get_clauses_ll (M, N, U, D, NP, WS, Q) ! j))
      (working_queue_list (S'M, N', U', S'D, NP', UP', WS', Q)))
      (S'M, N', U', S'D, NP', UP', WS', Q) =
      (S'M, N', U', S'D, NP', UP', remove1_mset (i, TWL_Clause [L, L'] UW) WS', Q)\<close>
    by (simp add: M'_def N'_def U'_def S NP'_def UP'_def WS'_def S')
  have LLUW_in_NP_N_D: \<open>TWL_Clause [L, L'] UW \<in> twl_clause_of_ll ` set (take NP N)\<close> if \<open>j < NP\<close>
    using N_j_in_NP[THEN imageI, of twl_clause_of_ll] N_j that by auto

  have update_clause_ll_spec:
    \<open>RETURN (NN[jj := update_clause_ll (NN ! jj) ii k], UU)
    \<le> \<Down> {((N, U), (N', U')). N' = twl_clause_of_ll `# mset (take NP N) \<and>
          U' = twl_clause_of_ll `# filter_mset (\<lambda>C. length C > 1) (mset (drop U N))}
      (SPEC (update_clauses_list (N'', U'') C i' k''))\<close>
    if k_2: \<open>k \<ge> 2\<close> and k'': \<open>k'' = k - 2\<close> and [simp]: \<open>i' = i\<close> \<open>N'' = N'\<close> \<open>U'' = U'\<close>
    \<open>C = (twl_clause_of_ll (get_clauses_ll (M, N, U, D, NP, WS, Q) ! j))\<close> \<open>NN = N\<close>
    \<open>jj = j\<close> \<open>ii = i\<close> \<open>UU = U\<close>
    for k k' k'' i'  jj ii :: nat and N'' U'' C NN UU
  proof cases
    obtain k' where k': \<open>k = Suc (Suc k')\<close>
      using k_2 by (cases k; cases \<open>k - 1\<close>) auto
    assume J_NP: \<open>j < NP\<close>
    have L_L'_UW_N: \<open>L # L' # UW \<in> set (take NP N)\<close>
      using J_NP N_j N_j_in_NP by auto
    have TWL_L_L'_UW_N: \<open>TWL_Clause [L, L'] UW \<in> twl_clause_of_ll ` set (take NP N)\<close>
      using imageI[OF L_L'_UW_N, of twl_clause_of_ll] by auto
    have H0: \<open>TWL_Clause [UW ! k', L'] (list_update UW k' L) =
      update_clause_list (TWL_Clause [L, L'] UW) i k'\<close> if \<open>i = 0\<close>
      using i by (auto simp: that)
    have H1: \<open>TWL_Clause [L, UW ! k'] (UW[k' := L']) =
      update_clause_list (TWL_Clause [L, L'] UW) i k'\<close> if \<open>i = 1\<close>
      using i by (auto simp: that)
    show ?thesis
      apply (rule RETURN_SPEC_refine)
      using J_NP j NP_U U_N i by (auto simp: mset_update update_clause_ll_def N_j_in_NP
          N_j_Suc_0 N_j_0 N_j k' U'_def N'_def image_mset_remove1_mset_if
          L_L'_UW_N H0 TWL_L_L'_UW_N H1 k''
          simp del: update_clause_list.simps
          intro!: update_clauses_list.intros)
  next
    obtain k' where k': \<open>k = Suc (Suc k')\<close>
      using k_2 by (cases k; cases \<open>k - 1\<close>) auto
    assume J_NP: \<open>\<not>j < NP\<close>
    then have \<open>U \<le> j\<close> and \<open>j< length N\<close>
      using j by auto
    have L_L'_UW_N: \<open>L # L' # UW \<in> set (drop U N)\<close>
      using N_j \<open>U \<le> j\<close> in_set_drop_conv_nth j by fastforce
    have TWL_L_L'_UW_N: \<open>TWL_Clause [L, L'] UW \<in> twl_clause_of_ll ` set (drop U N)\<close>
      using imageI[OF L_L'_UW_N, of twl_clause_of_ll] by auto
    have L_L'_UW: \<open>TWL_Clause [L, L'] UW \<in> twl_clause_of_ll ` {a \<in> set (drop U N). Suc 0 < length a}\<close>
    proof -
      have f1: "Suc 0 < length (N ! j)"
        using N_j_1 by presburger
      have "N ! j \<in> set (drop U N)"
        by (simp add: L_L'_UW_N N_j)
      then have "twl_clause_of_ll (N ! j) \<in> twl_clause_of_ll ` {ls \<in> set (drop U N). Suc 0 < length ls}"
        using f1 by blast
      then show ?thesis
        by simp
    qed
    have H0: \<open>TWL_Clause [UW ! k', L'] (list_update UW k' L) =
      update_clause_list (TWL_Clause [L, L'] UW) i k'\<close> if \<open>i = 0\<close>
      using i by (auto simp: that)
    have H1: \<open>TWL_Clause [L, UW ! k'] (UW[k' := L']) =
      update_clause_list (TWL_Clause [L, L'] UW) i k'\<close> if \<open>i = 1\<close>
      using i by (auto simp: that)
    show ?thesis
      apply (rule RETURN_SPEC_refine)
      using J_NP j NP_U U_N i by (auto simp: mset_update update_clause_ll_def N_j_in_NP
          N_j_Suc_0 N_j_0 N_j k' U'_def N'_def image_mset_remove1_mset_if drop_update_swap
          H0 H1 TWL_L_L'_UW_N L_L'_UW_N L_L'_UW k''
          simp del: update_clause_list.simps
          intro!: update_clauses_list.intros)
  qed
  have in_trail_all_defined: False if 
    \<open>Propagated K j \<in> set M\<close> and \<open>xb \<in> set UW\<close> and
    \<open>- xb \<notin> lits_of_l M\<close>
    for C xb K
  proof -
    have con: \<open>convert_lit_ll N (Propagated K j) \<in> convert_lit_ll N ` set M\<close>
      using that by blast
    then have \<open>K \<in> set (take 2 (N!j))\<close>
      using add_inv S' S that M'_def  S'M
      by (auto simp: additional_WS_invs_def)
    
    obtain M1 M2 where M12: \<open>convert_lits_ll_m N M = M2 @ Propagated K (N!j) # M1\<close>
      using con by (metis (no_types, lifting) \<open>Propagated K j \<in> set M\<close> convert_lit_ll.simps(2) 
          in_set_conv_decomp_first list.simps(9) map_append)
    from arg_cong[OF this, of set] have M12': \<open>convert_lit_ll N ` set M = set M2 \<union> {Propagated K (N!j)} \<union> set M1\<close>
      by auto
    have \<open>\<And>L mark a b. a @ Propagated L mark # b = trail (convert_to_state (twl_st_of S')) \<longrightarrow> b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def by fast
    from this[of _ K \<open>mset (N!j)\<close>] have M1: \<open>convert_lits_l M1 \<Turnstile>as CNot (remove1_mset K (mset (N!j)))\<close> and \<open>K \<in> set (N!j)\<close>
      using M12 unfolding S' by (auto simp: cdcl\<^sub>W_restart_mset_state S'M)
    have \<open>K \<in> set (take 2 (N ! j))\<close>
      using add_inv unfolding S' additional_WS_invs_def by (auto simp: cdcl\<^sub>W_restart_mset_state S'M M12')
    then have \<open>-xb \<in> lits_of_l M1\<close>
      using that M1 by (auto simp: true_annots_true_cls_def_iff_negation_in_model N_j)
    then have \<open>-xb \<in> lits_of_l M\<close>
      by (subst lits_of_convert_lit_ll[symmetric, of _ N], subst M12') auto
    then show False
      using that M12 by auto
  qed
  have \<open>U + (j - U) = j\<close> if \<open>j >= U\<close>
    using U_N N_j j that by auto
    
  have length_drup_U_N:  \<open>length (drop U N ! (j - U)) \<noteq> Suc 0\<close> if \<open>j >= U\<close>
    apply (subst nth_drop)
    using U_N N_j j that by auto
  have length_upd_cls: \<open>length (update_clause_ll (L # L' # UW) i k) \<noteq> Suc 0\<close> for k
    using i  by (cases k; cases \<open>k-1\<close>) (auto simp: update_clause_ll_def)
  have length_upd_N_j: \<open>length (update_clause_ll (L # L' # UW) i k) = length (N!j)\<close> for k
    using i  by (cases k; cases \<open>k-1\<close>) (auto simp: update_clause_ll_def N_j)
  obtain WSij where WSij: \<open>WS = add_mset (i, j) WSij\<close>
    using WS unfolding S by (auto dest: multi_member_split)
  have \<open>?C \<in> \<langle>{(S, S'). (S, S') \<in> twl_st_of_ll \<and> twl_clause_of_ll_inv S}\<rangle>nres_rel\<close>
    using remove_S[unfolded S, unfolded S']
    unfolding unit_propagation_inner_loop_body_ll_def unit_propagation_inner_loop_body_list_def
      S remove_S remove_S_ll S' remove_S[unfolded S, unfolded get_clauses_ll.simps, unfolded S']
    using [[goals_limit=1]]
    apply (refine_vcg valued_refinement update_clause_ll_spec
        find_unwatched_ll_spec[THEN refine_pair_to_SPEC_rev_eq', of _ _ _ _ N];
        remove_dummy_vars simp: remove_S S S')
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal using N_j i SS' S'M by auto
    subgoal using N_j i by auto
    subgoal using N_j i S'M by auto
    subgoal using N_j i S'M by auto
    subgoal using N_j i S'M by auto
    subgoal by (auto simp:)
    subgoal using N_j inv_ll[unfolded S] WS[unfolded S] S'M S' SS' S
      by (auto simp: twl_st_of_ll_def image_mset_remove1_mset_if dest: in_diffD)
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal using N_j i S'M by simp
    subgoal using S'M by auto
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal using N_j inv_ll[unfolded S] WS[unfolded S] S'M S' SS' S
      by (auto simp: twl_st_of_ll_def image_mset_remove1_mset_if dest: in_diffD)
    subgoal using N_j inv_ll[unfolded S] WS[unfolded S] S'M S' SS' S i
      by (auto simp: twl_st_of_ll_def image_mset_remove1_mset_if dest: in_diffD)
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal using N_j inv_ll[unfolded S] WS[unfolded S] S'M S' SS' S i apply clarify
      unfolding twl_st_of_ll_def Let_def twl_clause_of_ll_inv.simps prod.case
        get_clauses_ll.simps
      apply (simp (no_asm_simp) add: Ball_def)
      apply (intro conjI allI)
      subgoal for _ _ _ _ x
        apply (cases x)
        using S'M i apply (auto simp: nth_list_update' update_clause_ll_def)[]
        using S'M i apply (auto simp: nth_list_update' update_clause_ll_def simp: 
            dest!: in_trail_all_defined)[]
        done
      subgoal premises H for _ _ _ _ 
        apply (cases \<open>j < NP\<close>)
        using H S'M i apply (auto simp: nth_list_update' update_clause_ll_def)[]
        using H S'M i j apply (auto simp: nth_list_update' update_clause_ll_def simp: drop_update_swap
            dest: in_trail_all_defined)[]
        done
      subgoal
        using S'M i j U_N NP_U by (cases \<open>j < NP\<close>) (auto 0 4 simp: nth_list_update' update_clause_ll_def mset_update drop_update_swap
           mset_update simp: in_trail_all_defined) (* around 1 minute *)
      subgoal
        using S'M i j U_N NP_U 
        apply (cases \<open>j < NP\<close>)
        apply (simp (no_asm_simp) add: UP'_def; fail)
        apply (simp (no_asm_simp) add: UP'_def)
        
        apply (subst drop_update_swap)
         apply (simp;fail)
         apply (simp (no_asm_simp)add: nth_list_update' mset_update)
        apply (subst mset_update)
        using j apply (auto; fail)[]
        apply (simp add: length_drup_U_N length_upd_cls N_j)
        done
      subgoal
        using S'M i j U_N NP_U 
        (* apply (cases \<open>j < NP\<close>) *)
        using WS unfolding S working_queue_ll.simps apply (simp add: WS'_def image_mset_remove1_mset_if
            nth_list_update' mset_update)
        apply (simp add: length_drup_U_N length_upd_cls N_j nth_list_update' WSij)
        sorry 
      subgoal
        using S'M i j U_N NP_U 
        using WS unfolding S working_queue_ll.simps apply (simp add: WS'_def image_mset_remove1_mset_if
            nth_list_update' mset_update length_drup_U_N length_upd_cls N_j length_upd_N_j)
        by (blast dest: in_diffD)
      done
    done
  show ?thesis
    sorry
qed

end