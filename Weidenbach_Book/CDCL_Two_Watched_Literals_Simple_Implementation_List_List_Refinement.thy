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

fun take_between :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  \<open>take_between i j l = take (j - i) (drop i l)\<close>

fun twl_st_of_ll :: \<open>'v twl_st_ll  \<Rightarrow> 'v twl_st_list\<close> where
\<open>twl_st_of_ll S =
  (let (M, N, U, C, NP, WS, Q) = S;
        M' = convert_lits_ll N M;
        N' = twl_clause_of_ll `# mset (take NP N);
        U' = twl_clause_of_ll `# filter_mset (\<lambda>C. length C > 1) (mset (drop U N));
        UP' = mset `# filter_mset (\<lambda>C. length C = 1) (mset (drop U N));
        NP' = mset `# mset (take_between NP U N);
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

lemma find_unwatched_ll_spec: 
  \<open>(find_unwatched_ll, find_unwatched) \<in> {(M', M). M = convert_lits_ll N M'} \<rightarrow> {(C', C). C = unwatched_ll C' \<and> length C' \<ge> 2} \<rightarrow> 
  \<langle>{((found', i'), (found, i)). i' = i + 2 \<and> found' = found}\<rangle>nres_rel\<close>
proof -
  have val: \<open>valued M L \<le> \<Down> Id (valued M' L')\<close>
    if \<open>convert_lits_ll N M = M'\<close> and \<open>L = L'\<close> for M M' L L'
    using that by auto
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
  assumes \<open>(f, g) \<in> {(M', M). M = \<rho> M'} \<rightarrow> {(S', S). S = h S' \<and> R S'} \<rightarrow> \<langle>{((brk', S'), (brk, S)). S' = h' S \<and> brk' = brk}\<rangle>nres_rel\<close>
    (is \<open>_ \<in> _ \<rightarrow> ?R \<rightarrow> ?I\<close>)
  assumes \<open>R S\<close> and [simp]: \<open>S' = h S\<close> \<open>b = \<rho> a\<close>
  shows \<open>f a S \<le> \<Down> {((brk', S'), (brk, S)). S' = h' S \<and> brk' = brk} (g b S')\<close>
proof -
  have \<open>(f a S, g b S') \<in> ?I\<close>
    using assms unfolding fun_rel_def by auto
  then show ?thesis
    unfolding nres_rel_def fun_rel_def  pw_le_iff pw_conc_inres pw_conc_nofail
    by auto
qed
thm  find_unwatched_ll_spec[THEN refine_pair_to_SPEC_rev_eq']
 
  
lemma unit_propagation_inner_loop_body_list:
  assumes
    WS: \<open>(i, j) \<in># working_queue_ll S\<close> and
    struct_invs: \<open>twl_struct_invs (twl_st_of (twl_st_of_ll S))\<close> and
    C_N_U: \<open>twl_clause_of C \<in># get_clauses (twl_st_of (twl_st_of_ll S))\<close> and
    add_inv: \<open>additional_WS_invs (twl_st_of_ll S)\<close> and
    stgy_inv: \<open>twl_stgy_invs (twl_st_of (twl_st_of_ll S))\<close> and
    inv_ll: \<open>twl_clause_of_ll_inv S\<close>
  shows
  \<open>(unit_propagation_inner_loop_body_ll (i, j) (set_working_queue_ll (working_queue_ll S - {#(i, j)#}) S),
    unit_propagation_inner_loop_body_list (i, twl_clause_of_ll (get_clauses_ll S ! j))
      (set_working_queue_list (working_queue_list (twl_st_of_ll S) - {#(i, twl_clause_of_ll (get_clauses_ll S ! j))#}) (twl_st_of_ll S))
    ) \<in> \<langle>{(S, S'). S' = twl_st_of_ll S \<and> twl_clause_of_ll_inv S \<and> additional_WS_invs S' \<and> twl_stgy_invs (twl_st_of S') \<and> twl_struct_invs (twl_st_of S')}\<rangle> nres_rel\<close>
    (is \<open>?C \<in> _\<close>)
proof -
  obtain M N U D NP WS Q where
    S: \<open>S = (M, N, U, D, NP, WS, Q)\<close>
    by (cases S) auto
  define M' N' U' UP' NP' WS' where
     \<open>M' = convert_lits_ll N M\<close> and
     \<open>N' = twl_clause_of_ll `# mset (take NP N)\<close> and
     \<open>U' = twl_clause_of_ll `# filter_mset (\<lambda>C. length C > 1) (mset (drop U N))\<close> and
     \<open>UP' = mset `# filter_mset (\<lambda>C. length C = 1) (mset (drop U N))\<close> and
     \<open>NP' = mset `# mset (take_between NP U N )\<close> and
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
  have N_j_in_NP: \<open>N ! j \<in> set (take NP N)\<close> if \<open>j < NP\<close>
    using that by (metis NP_U U_N in_set_conv_nth length_take linear min_less_iff_conj nat_less_le nth_take)
  have j: \<open>(j < NP \<or> U \<le> j) \<and> j < length N\<close> and N_j_1: \<open>length (N!j) > 1\<close>
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
    [simp]: \<open>unwatched_ll (L # L' # UW) = UW\<close>
    by (auto simp: watched_ll_def N_j unwatched_ll_def)
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
  have nth_UW_N: \<open>UW ! k = (N!j) ! (k+2)\<close> for k
    using N_j by auto
  have N_j_upd_0: \<open>(N ! j)[k := N ! j ! 0, 0 := N ! j ! k] = [N ! j ! k, N ! j ! 1] @ (drop 2 ((N ! j)[k := N ! j ! 0]))\<close>
    if \<open>k \<ge> 2\<close> for k
    using that N_j by (cases k; cases \<open>k-1\<close>) auto
  have remove_S: \<open>set_working_queue_list
        (remove1_mset (i, twl_clause_of_ll (N ! j))
          (working_queue_list
            (twl_st_of_ll (M, N, U, D, NP, WS, Q))))
        (twl_st_of_ll (M, N, U, D, NP, WS, Q)) =
       (M', N', U', D, NP', UP', remove1_mset (i, TWL_Clause [L, L'] UW) WS', Q)\<close>
    by (simp add: M'_def N'_def U'_def S NP'_def UP'_def WS'_def)  
  have LLUW_in_NP_N_D: \<open>TWL_Clause [L, L'] UW \<in> twl_clause_of_ll ` set (take NP N)\<close> if \<open>j < NP\<close>
    using N_j_in_NP[THEN imageI, of twl_clause_of_ll] N_j that by auto
  
  have 
    \<open>RETURN (N[j := update_clause_ll (N ! j) i k], U)
    \<le> \<Down> {((N, U), (N', U')). N' = twl_clause_of_ll `# mset (take NP N) \<and> 
      U' = twl_clause_of_ll `# filter_mset (\<lambda>C. length C > 1) (mset (drop U N))}
        (SPEC
          (update_clauses_list (N', U')
            (twl_clause_of_ll
              (get_clauses_ll (M, N, U, D, NP, WS, Q) ! j))
            i (k - 2)))\<close>
    if \<open>k = Suc (Suc k')\<close>
    for k k'
    apply (rule RETURN_SPEC_refine)
    unfolding update_clauses_list.simps update_clause_ll_def apply auto
    apply (drule HOL.spec[of _ \<open>twl_clause_of_ll (N!j)\<close>])
    using j i that NP_U apply (auto simp: mset_update update_clauses_list.simps drop_update_swap N_j_upd_0
        N'_def U'_def)
            apply (subst (asm)image_mset_remove1_mset_if)
             apply (auto simp: N_j_in_NP N_j_Suc_0 numeral_2_eq_2[symmetric] nth_UW_N)[2]
    apply (auto simp: N_j)[]
            apply (auto dest: LLUW_in_NP_N_D)[]
            apply (subst (asm)image_mset_remove1_mset_if)
             apply (auto simp: N_j_in_NP N_j_Suc_0 numeral_2_eq_2[symmetric] nth_UW_N)[2]
    apply (auto simp: N_j)[]
            apply (auto dest!: LLUW_in_NP_N_D)[]
            apply (subst (asm)image_mset_remove1_mset_if)
             apply (auto simp: N_j_in_NP N_j_Suc_0 numeral_2_eq_2[symmetric] nth_UW_N)[2]
         apply (auto simp: N_j)[]
    apply (metis LLUW_in_NP_N_D mset.simps(2) mset_single twl_clause_of.simps)

    
  thm  HOL.spec[of _ \<open>N!j\<close>]
    oops
  have \<open>?C \<in> \<langle>{(S, S'). S' = twl_st_of_ll S \<and> twl_clause_of_ll_inv S}\<rangle>nres_rel\<close>
    unfolding unit_propagation_inner_loop_body_ll_def unit_propagation_inner_loop_body_list_def
      S remove_S remove_S_ll
    using [[goals_limit=1]]
    apply (refine_vcg valued_refinement find_unwatched_ll_spec[THEN refine_pair_to_SPEC_rev_eq', of _ _ _ N];
        remove_dummy_vars simp: remove_S_ll)
    subgoal using N_j i remove_S by auto
    subgoal using N_j i by auto
    subgoal using N_j i unfolding S by auto
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal by (auto simp:)
    subgoal using N_j inv_ll[unfolded S] WS[unfolded S] 
      by (auto simp: image_mset_remove1_mset_if dest: in_diffD)
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal using N_j i by simp
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal using N_j inv_ll[unfolded S] by auto
    subgoal using N_j i inv_ll[unfolded S] WS[unfolded S] 
      by (auto simp: image_mset_remove1_mset_if dest: in_diffD)
    subgoal using N_j i sorry
    subgoal using N_j i sorry
      (* apply (auto simp add: ) *)
  thm valued_refinement find_unwatched_ll_spec[THEN refine_pair_to_SPEC_rev_eq', of _ _ _ N]
  oops by auto
    subgoal using N_j i by auto
    subgoal
      oops

end