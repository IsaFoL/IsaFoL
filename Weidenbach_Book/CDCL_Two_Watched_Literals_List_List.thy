theory CDCL_Two_Watched_Literals_List_List
  imports CDCL_Two_Watched_Literals_List_Inner
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

definition twl_clause_of_l where
  \<open>twl_clause_of_l C = TWL_Clause (mset (watched_l C)) (mset (unwatched_l C))\<close>

(* TODO: we do not need to convert to multiset: we cannot update a clause that has been put
  on the trail.
  And ensuring that the true literal is at position 0 might be useful\<dots>*)
fun convert_lit_ll :: \<open>'v literal list list \<Rightarrow> ('v, nat) ann_lit \<Rightarrow> ('v, 'v clause twl_clause) ann_lit\<close> where
  \<open>convert_lit_ll _ (Decided K) = Decided K\<close>
| \<open>convert_lit_ll N (Propagated K i) = Propagated K (twl_clause_of_l (N!i))\<close>

definition convert_lits_ll_m where
  \<open>convert_lits_ll_m  N = map (convert_lit_ll N)\<close>

fun convert_lit_l :: \<open>('v, 'v clause_list) ann_lit \<Rightarrow> ('v, 'v clause twl_clause) ann_lit\<close> where
  \<open>convert_lit_l (Decided K) = Decided K\<close>
| \<open>convert_lit_l (Propagated K C) = Propagated K (twl_clause_of_l C)\<close>

definition convert_lits_l_m where
  \<open>convert_lits_l_m M = map convert_lit_l M\<close>

fun take_between :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  \<open>take_between i j l = take (j - i) (drop i l)\<close>

text \<open>The two states are related if... TODO.\<close>
definition twl_st_of_ll :: \<open>('v twl_st_ll \<times> 'v twl_st_list) set\<close> where
\<open>twl_st_of_ll = {(S', S).
  (let (M, N, U, C, NP, WS, Q) = S';
       (M', N', U', C', NP', UP', WS', Q') = S;
        SM' = convert_lits_ll_m  N M;
        S'M' = convert_lits_l_m M';
        SN' = twl_clause_of_ll `# mset (take NP N);
        SU' = twl_clause_of_ll `# filter_mset (\<lambda>C. length C > 1) (mset (drop U N));
        SUP' = mset `# filter_mset (\<lambda>C. length C = 1) (mset (drop U N));
        SNP' = mset `# mset (take_between NP U N);
        SWS' = (\<lambda>(i, j). (i, twl_clause_of_ll (N!j))) `# WS;
        SC = map_option mset C;
        S'C' = map_option mset C'
    in
  (SM', SN', SU', SC, SNP', SUP', SWS', Q) = (S'M', N', U', S'C', NP', UP', WS', Q'))}
\<close>

text \<open>
  \<^item> The annotation in the trail are valid indexes in the list.
  \<^item> The indices in the working queue are distinct. This does not say anything about
  the number of clauses.
  \<^item> The working queue points to clauses of size \<open>\<ge> 2\<close>.
  \<^item> The clauses are in the order: first the init clauses of size \<open>\<ge> \<close>2, then those of size 1, after
  that the learned clauses (without sorting).\<close>

fun twl_clause_of_ll_inv where
  \<open>twl_clause_of_ll_inv (M, N, U, C, NP, WS, Q) \<longleftrightarrow>
    (\<forall>L i. Propagated L i \<in> set M \<longrightarrow> i < length N) \<and>
    (\<forall>(i, j) \<in># WS. (j < NP \<or> j \<ge> U) \<and> j < length N \<and> length (N!j) > 1) \<and>
    NP \<le> U \<and> U \<le> length N \<and> distinct_mset WS \<and>
    (\<forall>i i' j j'. (i, j) \<in># WS \<longrightarrow> (i', j') \<in># WS \<longrightarrow> i = i')\<and>
    (\<forall>i j. (i, j) \<in># WS \<longrightarrow> j < length N)\<close>

declare twl_clause_of_ll_inv.simps[simp del]

lemma lit_of_convert_lit_ll[simp]: \<open>lit_of (convert_lit_ll S C) = lit_of C\<close>
  by (cases C) auto

fun twl_clause_of_ll_m where
  \<open>twl_clause_of_ll_m (Decided K) = Decided K\<close>
| \<open>twl_clause_of_ll_m (Propagated K C) = Propagated K (watched C + unwatched C)\<close>

lemma convert_lit_convert_lit_l: \<open>convert_lit a = twl_clause_of_ll_m (convert_lit_l a)\<close>
  by (cases a) (auto simp: watched_def unwatched_def twl_clause_of_l_def mset_append[symmetric]
    simp del: mset_append split!: twl_clause.splits)

lemma convert_lits_l_convert_lits_l_m: \<open>convert_lits_l M = map twl_clause_of_ll_m (convert_lits_l_m M)\<close>
  by (induction M) (auto simp: convert_lit_convert_lit_l convert_lits_l_m_def)

lemma lits_of_convert_lit_ll[simp]: \<open>lits_of (convert_lit_ll S ` M) = lits_of M\<close>
  unfolding lits_of_def by (auto simp: image_image)

lemma lits_of_l_convert_lit_ll[simp]: \<open>lits_of_l (convert_lits_ll_m S M) = lits_of_l M\<close>
  unfolding lits_of_def by (auto simp: image_image convert_lits_ll_m_def)

lemma defined_lit_convert_lits_ll_m [iff]: \<open>defined_lit (convert_lits_ll_m  S M) L \<longleftrightarrow> defined_lit M L\<close>
  by (auto simp: Decided_Propagated_in_iff_in_lits_of_l convert_lits_ll_m_def)

lemma valued_convert_lits_ll_m [simp]: \<open>valued (convert_lits_ll_m  S M) L = valued M L\<close>
  unfolding valued_def by (auto simp: )

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

lemma convert_lits_l_m_convert_lits_l_m_lits_of_eq:
  assumes \<open>convert_lits_l_m M' = convert_lits_ll_m N M\<close>
  shows \<open>lits_of_l M = lits_of_l M'\<close>
  supply convert_lits_l_m_def[simp] convert_lits_ll_m_def[simp]
  using assms
  apply (induction M arbitrary: M' rule: ann_lit_list_induct)
  subgoal by simp
  subgoal for L M M' by (cases M'; cases \<open>hd M'\<close>) auto
  subgoal for L M C M' by (cases M'; cases \<open>hd M'\<close>) auto
  done

lemma convert_lits_l_m_convert_lits_l_m_defined_lit_eq:
  assumes \<open>convert_lits_l_m M' = convert_lits_ll_m N M\<close>
  shows \<open>defined_lit M L = defined_lit M' L\<close>
  using assms by (auto simp: convert_lits_l_m_convert_lits_l_m_lits_of_eq 
      Decided_Propagated_in_iff_in_lits_of_l)

lemma find_unwatched_ll_spec:
  \<open>(find_unwatched_ll, find_unwatched) \<in> {(M', M). convert_lits_l_m M = convert_lits_ll_m N M'} \<rightarrow>
    {(C', C). C = unwatched_ll C' \<and> length C' \<ge> 2} \<rightarrow>
    \<langle>{((found', i'), (found, i)). i' = i + 2 \<and> found' = found}\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow> _ \<rightarrow> _\<close>)
proof -
  have val: \<open>valued M' L \<le> \<Down> Id (valued M L')\<close>
    if \<open>(M', M) \<in> ?R\<close> and \<open>L = L'\<close> for M :: \<open>('a, 'a literal list) ann_lits\<close> and
    M' :: \<open>('a, nat) ann_lits\<close> and L L'
    using that by (auto simp: valued_def convert_lits_l_m_convert_lits_l_m_lits_of_eq
        Decided_Propagated_in_iff_in_lits_of_l)
  show ?thesis
    unfolding find_unwatched_ll_def find_unwatched_def
    apply (refine_rcg val)
    subgoal by auto
    subgoal by auto
    subgoal for M M' C' C fi' fi
      by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists convert_lits_l_m_convert_lits_l_m_lits_of_eq)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists convert_lits_l_m_convert_lits_l_m_lits_of_eq
          Decided_Propagated_in_iff_in_lits_of_l)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists)
    subgoal by (auto simp: unwatched_ll_def list_length_ge_2_exists convert_lits_l_m_convert_lits_l_m_lits_of_eq)
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
    unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
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

lemma truc:
  assumes
    \<open>(f', f) \<in> R \<rightarrow> \<langle>P\<rangle> nres_rel\<close>
  assumes
    \<open>(f, fg) \<in> R' \<rightarrow> \<langle>Q\<rangle> nres_rel\<close>
  shows
    \<open>(f', fg) \<in> R O R' \<rightarrow> \<langle>P O Q\<rangle> nres_rel\<close>
  using relcomp.relcompI[OF assms(1,2)]
  using fun_rel_comp_dist[of R \<open>\<langle>P\<rangle>nres_rel\<close>  R' \<open>\<langle>Q\<rangle>nres_rel\<close>] unfolding nres_rel_comp
  by (meson subsetCE)

lemma truc':
  assumes
    \<open>(f', f) \<in> \<langle>P\<rangle> nres_rel\<close>
  assumes
    \<open>(f, fg) \<in> \<langle>Q\<rangle> nres_rel\<close>
  shows
    \<open>(f', fg) \<in> \<langle>P O Q\<rangle> nres_rel\<close>
  using relcomp.relcompI[OF assms(1,2)] unfolding nres_rel_comp
  by (meson subsetCE)

lemma refine_add_inv_in_set:
  fixes f' :: \<open>'a \<Rightarrow> 'c nres\<close> and f :: \<open>'b \<Rightarrow> 'd nres\<close> and H :: \<open>('a \<times> 'b) set\<close>  and
    H' :: \<open>('c \<times> 'd) set\<close>
  assumes
    \<open>(f', f) \<in> {(S, S'). (S, S') \<in> H \<and> R S} \<rightarrow> \<langle>{(T, T'). (T, T') \<in> H' \<and> P' T}\<rangle> nres_rel\<close>
    (is \<open>_ \<in> ?R \<rightarrow> _\<close>)
  assumes
    \<open>\<And>S S'. (S, S') \<in> H \<Longrightarrow> R S \<Longrightarrow> f S' \<le> SPEC (\<lambda>T. Q T)\<close>
  shows
    \<open>(f', f) \<in> ?R \<rightarrow> \<langle>{(T, T'). (T, T') \<in> H' \<and> P' T \<and> Q T'}\<rangle> nres_rel\<close>
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
  by fastforce

lemma refine_add_invariants_in_set:
  assumes
    \<open>f S \<le> SPEC(\<lambda>S'. Q S')\<close> and
    \<open>y \<le> \<Down> {(S, S'). (S, S') \<in> H \<and> P S} (f S)\<close>
  shows \<open>y \<le> \<Down> {(S, S'). (S, S') \<in> H \<and> P S \<and> Q S'} (f S)\<close>
  using assms unfolding pw_le_iff pw_conc_inres pw_conc_nofail by force

lemma Down_mono: \<open>P \<subseteq> P' \<Longrightarrow> \<Down> P f \<le> \<Down> P' f\<close>
  by (meson pw_conc_inres pw_conc_nofail pw_ref_I subsetCE)

lemma refine_add_inv_in_set_no_arg:
  fixes f' :: \<open>'c nres\<close> and f :: \<open>'d nres\<close> and H' :: \<open>('c \<times> 'd) set\<close>
   assumes
    \<open>(f', f) \<in> \<langle>{(T, T'). (T, T') \<in> H' \<and> P' T}\<rangle> nres_rel\<close>
   assumes
    \<open>(f, fg) \<in> \<langle>{(T, T'). (T, T') \<in> H'' \<and> Q T}\<rangle> nres_rel\<close> and
    \<open>nofail fg\<close>
   shows
    \<open>(f', f) \<in>  \<langle>{(T, T'). (T, T') \<in> H' \<and> P' T \<and> Q T'}\<rangle> nres_rel\<close>
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
  by auto

lemma no_dup_propagate_propagated_eq:
  assumes 
    \<open>no_dup M\<close> and 
    \<open>Propagated K i \<in> set M\<close>
  shows
    \<open>Propagated K j \<in> set M \<longleftrightarrow> i = j\<close>
proof
  assume \<open>i = j\<close>
  then show \<open>Propagated K j \<in> set M\<close>
    using assms by auto
next
  assume \<open>Propagated K j \<in> set M\<close>
  then show \<open>i = j\<close>
    using distinct_map_eq[of \<open>\<lambda>l. atm_of (lit_of l)\<close> M \<open>Propagated K j\<close> \<open>Propagated K i\<close>]
    using assms by (auto simp: no_dup_def)
qed

lemma lit_of_twl_clause_of_ll_m[simp]: \<open>lit_of (twl_clause_of_ll_m a) = lit_of a\<close>
  by (cases a) auto

lemma lits_of_twl_clause_of_ll_m[simp]: \<open>lits_of (twl_clause_of_ll_m ` set M1) = lits_of_l M1\<close>
  by (induction M1) auto

lemma Propagated_conver_lit_l_eq: 
  \<open>Propagated K C = convert_lit_l x \<longleftrightarrow> (\<exists>C'. x = Propagated K C' \<and> C = twl_clause_of_l C')\<close>
  by (cases x) auto

lemma unit_propagation_inner_loop_body_list:
  assumes
    WS: \<open>(i, j) \<in># working_queue_ll S\<close> and
    struct_invs: \<open>twl_struct_invs (twl_st_of S')\<close> and
    SS': \<open>(S, S') \<in> twl_st_of_ll\<close> and
    add_inv: \<open>additional_WS_invs S'\<close> and
    stgy_inv: \<open>twl_stgy_invs (twl_st_of S')\<close> and
    inv_ll: \<open>twl_clause_of_ll_inv S\<close>
  shows
  \<open>(unit_propagation_inner_loop_body_ll (i, j) (set_working_queue_ll (working_queue_ll S - {#(i, j)#}) S),
    unit_propagation_inner_loop_body_list (i, twl_clause_of_ll (get_clauses_ll S ! j))
      (set_working_queue_list (working_queue_list S' - {#(i, twl_clause_of_ll (get_clauses_ll S ! j))#}) S')
    ) \<in>
    \<langle>{(S, S'). (S, S') \<in> twl_st_of_ll \<and> twl_clause_of_ll_inv S \<and> additional_WS_invs S'  \<and>
      twl_struct_invs (twl_st_of S') \<and> twl_stgy_invs (twl_st_of S')}\<rangle> nres_rel\<close>
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
    S'M: \<open>convert_lits_l_m S'M = convert_lits_ll_m N M\<close>
    using SS' by (auto simp: twl_st_of_ll_def S S' N'_def U'_def UP'_def NP'_def WS'_def)
  then have D: \<open>D = None\<close>
    using struct_invs WS S S' by (auto simp: twl_struct_invs_def WS'_def)

  have i: \<open>i = 0 \<or> i = 1\<close>
    using WS add_inv SS' unfolding S by (auto simp: additional_WS_invs_def twl_st_of_ll_def)
  have NP_U: \<open>NP \<le> U\<close> and U_N: \<open>U \<le> length N\<close> and dist: \<open>distinct_mset WS\<close> and
    uniq_lit_WS: \<open>\<forall>i i' j j'. (i, j) \<in># WS \<longrightarrow> (i', j') \<in># WS \<longrightarrow> i = i'\<close>
    using inv_ll unfolding S by (auto simp: twl_clause_of_ll_inv.simps)
  have dist_q: \<open>distinct_queued (twl_st_of S')\<close> and w_q_inv: \<open>working_queue_inv (twl_st_of S')\<close>
    using struct_invs unfolding twl_struct_invs_def by fast+
  have i_N_j_WS': \<open>(i, twl_clause_of_ll (N!j)) \<in># WS'\<close>
    using WS unfolding WS'_def S by auto
  have N_j_in_NP: \<open>N ! j \<in> set (take NP N)\<close> if \<open>j < NP\<close>
    using that by (metis NP_U U_N in_set_conv_nth length_take linear min_less_iff_conj nat_less_le nth_take)
  have j: \<open>(j < NP \<or> U \<le> j)\<close>\<open>j < length N\<close> and N_j_1: \<open>length (N!j) > 1\<close>
    using inv_ll WS unfolding S N'_def U'_def by (auto simp: twl_clause_of_ll_inv.simps)
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
    if \<open>convert_lits_l_m M2 = convert_lits_ll_m  N M1\<close> and \<open>M1 = M\<close> and \<open>N' = N\<close> and \<open>j' = j\<close> and \<open>j'' = j\<close> and
    \<open>C' = twl_clause_of_ll (N' ! j'')\<close> and \<open>i' = i\<close> and \<open>i'' = i\<close>
    for M1 :: \<open>('a, nat) ann_lits\<close> and M2 :: \<open>('a, 'a literal list) ann_lit list\<close> and N' and
    j' j'' i' i'' :: nat and C'
    using that i N_j S by (auto simp: valued_def Decided_Propagated_in_iff_in_lits_of_l 
        convert_lits_l_m_convert_lits_l_m_lits_of_eq)
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

    then obtain M1 M2 where M12: \<open>convert_lits_ll_m N M = M2 @ convert_lit_ll N (Propagated K j) # M1\<close>
       using in_set_conv_decomp_first[of \<open>convert_lit_ll N (Propagated K j)\<close> \<open>convert_lits_ll_m N M\<close>]
       by (auto simp: convert_lits_ll_m_def)
    from arg_cong[OF this, of set] 
    have M12': \<open>convert_lit_ll N ` set M = set M2 \<union> convert_lit_l ` {Propagated K (N!j)} \<union> set M1\<close>
      by (auto simp: convert_lits_ll_m_def)
    have N_j_w_unw: \<open>mset (N!j) = watched (twl_clause_of_l (N ! j)) + unwatched (twl_clause_of_l (N ! j))\<close>
      by (auto simp: twl_clause_of_l_def mset_append[symmetric] simp del: mset_append)

    have \<open>\<And>L mark a b. a @ Propagated L mark # b = trail (convert_to_state (twl_st_of S')) \<longrightarrow> b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def by fast
    from this[of _ K \<open>mset (N!j)\<close>] have M1: \<open>map twl_clause_of_ll_m M1 \<Turnstile>as CNot (remove1_mset K (mset (N!j)))\<close> and 
      \<open>K \<in> set (N!j)\<close>
      unfolding S'  by (auto simp: cdcl\<^sub>W_restart_mset_state convert_lits_l_convert_lits_l_m N_j_w_unw[symmetric]
          S'M M12)
    have \<open>\<exists>C'. Propagated K C' \<in> set S'M \<and> mset (watched_l C') = mset (watched_l (N!j))\<close>
      using imageI[OF \<open>Propagated K j \<in> set M\<close>, of \<open>convert_lit_ll N\<close>]
      arg_cong[OF S'M, of set, symmetric]
      by (auto simp: convert_lits_l_m_def convert_lits_ll_m_def Propagated_conver_lit_l_eq 
          twl_clause_of_l_def simp del: watched_l.simps unwatched_l.simps) blast (* TODO What is going on here? *)
    then have \<open>K \<in> set (watched_l (N ! j))\<close>
      using add_inv unfolding S' additional_WS_invs_def by (auto simp: cdcl\<^sub>W_restart_mset_state S'M M12'
          simp del: watched_l.simps dest!: mset_eq_setD)
    then have \<open>-xb \<in> lits_of_l M1\<close>
      using that M1 by (auto simp: true_annots_true_cls_def_iff_negation_in_model N_j)
    then have \<open>-xb \<in> lits_of_l M\<close>
      by (subst lits_of_convert_lit_ll[symmetric, of _ N], subst M12') auto
    then show False
      using that M12 by auto
  qed
  have \<open>U + (j - U) = j\<close> if \<open>j \<ge> U\<close>
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
  then have i_j_WSij: \<open>(i, j) \<notin># WSij\<close>
    using dist by auto
  then have j_notin_WSij: \<open>(x, j) \<notin># WSij\<close> for x
    using WSij uniq_lit_WS by auto
  have L_L'_UW_in_N'_U': \<open>TWL_Clause {#L, L'#} (mset UW) \<in> twl_clause_of ` set_mset (N' + U')\<close>
    by (metis \<open>twl_clause_of_ll (N ! j) = TWL_Clause [L, L'] UW\<close> \<open>twl_clause_of_ll (N ! j) \<in># N' + U'\<close>
        image_iff mset.simps(2) mset_zero_iff_right twl_clause_of.simps)
  have H: \<open>unit_propagation_inner_loop_body_list
     (i,
      twl_clause_of_ll (get_clauses_ll S ! j))
     (set_working_queue_list
       (remove1_mset
         (i,
          twl_clause_of_ll
           (get_clauses_ll S ! j))
         (working_queue_list S'))
       S')
    \<le> \<Down> {(S, S').
          S' = twl_st_of S \<and>
          additional_WS_invs S \<and>
          twl_stgy_invs S' \<and>
          twl_struct_invs S'}
        (unit_propagation_inner_loop_body
          (watched
            (twl_clause_of_ll
              (get_clauses_ll S ! j)) !
           i,
           twl_clause_of
            (twl_clause_of_ll
              (get_clauses_ll S ! j)))
          (set_working_queue
            (remove1_mset
              (watched
                (twl_clause_of_ll
                  (get_clauses_ll S ! j)) !
               i,
               twl_clause_of
                (twl_clause_of_ll
                  (get_clauses_ll S ! j)))
              (working_queue (twl_st_of S')))
            (twl_st_of S')))\<close>
    apply (rule unit_propagation_inner_loop_body_list)
    using WS S' S i_N_j_WS' i struct_invs stgy_inv  L_L'_UW_in_N'_U' add_inv by (auto simp:)
  let ?CTRUC = \<open>twl_clause_of_ll (get_clauses_ll S ! j)\<close>
  have H':
    \<open>(unit_propagation_inner_loop_body_list (i, ?CTRUC) (set_working_queue_list (remove1_mset (i, ?CTRUC) (working_queue_list S')) S'),
   unit_propagation_inner_loop_body (watched ?CTRUC ! i, twl_clause_of ?CTRUC) (set_working_queue (remove1_mset (watched ?CTRUC ! i, twl_clause_of ?CTRUC) (working_queue (twl_st_of S'))) (twl_st_of S')))
  \<in> \<langle>{(S, S'). S' = twl_st_of S \<and> additional_WS_invs S \<and> twl_stgy_invs S' \<and> twl_struct_invs S'}\<rangle>nres_rel\<close>
    apply (rule unit_propagation_inner_loop_body_list2)
    using WS S' S i_N_j_WS' i struct_invs stgy_inv  L_L'_UW_in_N'_U' add_inv by (auto simp:)
  have R: \<open>?C \<in> \<langle>{(S, S'). (S, S') \<in> twl_st_of_ll \<and> twl_clause_of_ll_inv S}\<rangle>nres_rel\<close>
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
    subgoal using N_j i S'M by (auto simp: convert_lits_l_m_convert_lits_l_m_lits_of_eq)
    subgoal using N_j i S'M by (auto simp: convert_lits_l_m_convert_lits_l_m_lits_of_eq)
    subgoal using N_j i S'M by (auto simp: convert_lits_l_m_convert_lits_l_m_lits_of_eq 
          convert_lits_l_m_convert_lits_l_m_defined_lit_eq)
    subgoal by (auto simp:)
    subgoal using N_j inv_ll[unfolded S] WS[unfolded S] S'M S' SS' S
      by (auto simp: twl_st_of_ll_def image_mset_remove1_mset_if WSij twl_clause_of_ll_inv.simps)
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal using N_j i S'M by simp
    subgoal using S'M by (auto simp: convert_lits_l_m_convert_lits_l_m_lits_of_eq)
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal using N_j inv_ll[unfolded S] WS[unfolded S] S'M S' SS' S
      by (auto simp: twl_st_of_ll_def image_mset_remove1_mset_if twl_clause_of_ll_inv.simps dest: in_diffD)
    subgoal using N_j inv_ll[unfolded S] WS[unfolded S] S'M S' SS' S i
      (* by (auto simp: twl_st_of_ll_def image_mset_remove1_mset_if WSij twl_clause_of_ll_inv.simps) *)
      (* 1min *)
      sorry
    subgoal using N_j i by auto
    subgoal using N_j i by auto
    subgoal using N_j inv_ll[unfolded S] WS[unfolded S] S'M S' SS' S i apply clarify
      unfolding twl_st_of_ll_def Let_def twl_clause_of_ll_inv.simps prod.case
        get_clauses_ll.simps
      sorry (*
      apply (simp (no_asm_simp) add: Ball_def)
      apply (intro conjI allI)
      subgoal sorry
      subgoal for _ _ _  x
        apply (cases x)
        using S'M i apply (auto simp: nth_list_update' update_clause_ll_def; fail)[]
        using S'M i by (auto simp: nth_list_update' update_clause_ll_def simp:
            dest!: in_trail_all_defined)[]
      subgoal
        using S'M i j S'D by (cases \<open>j < NP\<close>) (auto simp: nth_list_update' update_clause_ll_def simp: drop_update_swap
            dest: in_trail_all_defined)
      subgoal
        using S'M i j U_N NP_U by (cases \<open>j < NP\<close>) (auto 0 4 simp: nth_list_update' update_clause_ll_def mset_update drop_update_swap
           mset_update simp: in_trail_all_defined) (* around 1 minute *)
      subgoal
        sorry
      subgoal
        sorry
      subgoal
        using S'M i j U_N NP_U
        apply (cases \<open>j < NP\<close>)
        apply (simp (no_asm_simp) add: UP'_def; fail)
        apply (simp (no_asm_simp) add: UP'_def)

        apply (subst drop_update_swap)
         apply (simp;fail)
         apply (simp (no_asm_simp)add: nth_list_update' mset_update)
        apply (subst mset_update)
        using j (* apply (auto; fail)[]
        apply (simp add: length_drup_U_N length_upd_cls N_j)
        done *) sorry
      subgoal
        using S'M i j U_N NP_U
        (* apply (cases \<open>j < NP\<close>) *)
        using WS unfolding S working_queue_ll.simps apply (simp add: WS'_def image_mset_remove1_mset_if
            nth_list_update' mset_update)
        apply (simp (no_asm_use) add: length_drup_U_N length_upd_cls N_j nth_list_update' WSij)
        apply (intro image_mset_cong_pair)
      using j_notin_WSij apply (simp (no_asm_use))
      by metis
      subgoal
        using S'M i j U_N NP_U
        using WS unfolding S working_queue_ll.simps apply (simp add: WS'_def image_mset_remove1_mset_if
            nth_list_update' mset_update length_drup_U_N length_upd_cls N_j length_upd_N_j)
        by (blast dest: in_diffD)
      subgoal
        by (meson in_diffD)
      subgoal
        by (meson in_diffD)
      done*)
    done
  have nf: \<open>nofail (unit_propagation_inner_loop_body (watched (twl_clause_of_ll (get_clauses_ll S ! j)) ! i, twl_clause_of (twl_clause_of_ll (get_clauses_ll S ! j)))
             (set_working_queue (remove1_mset (watched (twl_clause_of_ll (get_clauses_ll S ! j)) ! i, twl_clause_of (twl_clause_of_ll (get_clauses_ll S ! j))) (working_queue (twl_st_of S'))) (twl_st_of S')))\<close>
    apply (rule unit_propagation_inner_loop_body(2))
    using imageI[OF i_N_j_WS', of \<open>(\<lambda>(a, b). (watched b ! a, twl_clause_of b))\<close>]
    using WS S' S i_N_j_WS' i struct_invs stgy_inv  L_L'_UW_in_N'_U' add_inv D S'D by (auto simp:)
  show ?thesis
    apply (rule refine_add_inv_in_set_no_arg[where H'' = \<open>{(S, S'). S' = twl_st_of S}\<close>
          and fg = \<open>(unit_propagation_inner_loop_body
          (watched
            (twl_clause_of_ll
              (get_clauses_ll S ! j)) !
           i,
           twl_clause_of
            (twl_clause_of_ll
              (get_clauses_ll S ! j)))
          (set_working_queue
            (remove1_mset
              (watched
                (twl_clause_of_ll
                  (get_clauses_ll S ! j)) !
               i,
               twl_clause_of
                (twl_clause_of_ll
                  (get_clauses_ll S ! j)))
              (working_queue (twl_st_of S')))
            (twl_st_of S')))\<close>])
      apply (rule R)
    using H apply (auto intro!: nres_relI simp: weaken_SPEC)[]
    apply (erule order_trans)
     apply (rule Down_mono)
    apply auto[]
     using nf apply auto[]
    done
qed


definition unit_propagation_outer_loop_ll :: "'v twl_st_ll \<Rightarrow> 'v twl_st_ll nres"  where
  \<open>unit_propagation_outer_loop_ll S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_clause_of_ll_inv S\<^esup>
      (\<lambda>S. working_queue_ll S \<noteq> {#})
      (\<lambda>S. do {
        C \<leftarrow> SPEC (\<lambda>C. C \<in># working_queue_ll S);
        let S' = set_working_queue_ll (working_queue_ll S - {#C#}) S;
        unit_propagation_inner_loop_body_ll C S'
      })
      S\<^sub>0
  \<close>

lemma unit_propagation_outer_loop_ll_spec:
  \<open>(unit_propagation_outer_loop_ll, unit_propagation_inner_loop_list) \<in>
  {(S, S'). (S, S') \<in> twl_st_of_ll \<and> twl_clause_of_ll_inv S \<and> twl_struct_invs (twl_st_of S') \<and> twl_stgy_invs (twl_st_of S') \<and>
  additional_WS_invs S'} \<rightarrow>
  \<langle>{(T, T'). (T, T') \<in> twl_st_of_ll \<and> twl_clause_of_ll_inv T \<and>
  additional_WS_invs T' \<and> twl_struct_invs (twl_st_of T') \<and> twl_stgy_invs (twl_st_of T')}\<rangle> nres_rel\<close>
proof -
  have C_spec: \<open>SPEC (\<lambda>C. C \<in># working_queue_ll S) \<le> \<Down> {((i, j), (i', C')). i = i' \<and> twl_clause_of_ll (get_clauses_ll S ! j) = C'} (SPEC (\<lambda>C. C \<in># working_queue_list S'))\<close>
    if \<open>(S, S') \<in> twl_st_of_ll\<close>
    for S S'
    apply (rule RES_refine)
    apply (cases S, cases S')
    using that apply (force simp: twl_st_of_ll_def case_prod_beta)
    done
  show ?thesis
    unfolding unit_propagation_outer_loop_ll_def unit_propagation_inner_loop_list_def
    apply (refine_vcg C_spec)
    subgoal by auto[]
    subgoal by auto[]
    subgoal for S S' by (cases S, cases S') (auto simp add: twl_st_of_ll_def)
    subgoal by auto[]
    subgoal for S S' T T' C C'
      apply simp
      using unit_propagation_inner_loop_body_list[of \<open>fst C\<close> \<open>snd C\<close> T T']
      by (auto simp: nres_rel_def)
    done
qed

fun get_trail_ll :: "'v twl_st_ll \<Rightarrow> ('v, nat) ann_lit list"  where
  \<open>get_trail_ll (M, N, U, D, NP, WS, Q) = M\<close>


definition skip_and_resolve_loop_ll :: "'v twl_st_ll \<Rightarrow> 'v twl_st_ll nres"  where
  \<open>skip_and_resolve_loop_ll S\<^sub>0 =
    do {
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S). twl_clause_of_ll_inv S\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_ll S)))
        (\<lambda>(_, S).
          let (M, N, U, D, NP, WS, Q) = S in
          do {
            ASSERT(M \<noteq> []);
            let D' = the (get_conflict_ll S);
            (L, C) \<leftarrow> SPEC(\<lambda>(L, C). \<forall>i. Propagated L i = hd (get_trail_ll S) \<and>  C = N!i);
            if -L \<notin># mset D' then
              do {RETURN (False, (tl M, N, U, D, NP, WS, Q))}
            else
              if get_maximum_level M (remove1_mset (-L) (mset D')) = count_decided M
              then
                do {RETURN (resolve_cls_list L D' C = [],
                   (tl M, N, U, Some (resolve_cls_list L D' C), NP, WS, Q))}
              else
                do {RETURN (True, S)}
          }
        )
        (get_conflict_ll S\<^sub>0 = Some [], S\<^sub>0);
      RETURN S
    }
  \<close>

lemma get_conflict_ll_iff:
  assumes \<open>(a, a') \<in> twl_st_of_ll\<close>
  shows \<open>get_conflict_ll a = Some [] \<longleftrightarrow> get_conflict_list a' = Some []\<close>
  using assms apply (cases a, cases a', cases \<open>get_conflict_list a'\<close>)
  by (auto simp:twl_st_of_ll_def)

lemma is_decided_convert_lit_ll[iff]: \<open>is_decided (convert_lit_ll b z) \<longleftrightarrow> is_decided z\<close>
  by (cases z) auto

lemma is_decided_hg_get_trail_ll_iff:
  assumes \<open>(a, a') \<in> twl_st_of_ll\<close> and \<open>get_trail (twl_st_of a') \<noteq> []\<close>
  shows \<open>is_decided (hd (get_trail_ll a)) \<longleftrightarrow>  is_decided (hd (get_trail_list a'))\<close>
  using assms apply (cases a, cases a', cases \<open>get_trail_list a'\<close>)
  by (auto simp:twl_st_of_ll_def)


lemma count_decided_convert_lits_ll_m[simp]:
  \<open>count_decided (convert_lits_ll_m N' M') = count_decided M'\<close>
  by (induction M') auto

lemma get_level_convert_lits_ll_m[simp]: \<open>get_level (convert_lits_ll_m N' M') = get_level M'\<close>
  by (induction M' rule: ann_lit_list_induct)  (auto simp: get_level_cons_if)

lemma get_maximum_level_convert_lits_ll_m[simp]:
  \<open>get_maximum_level (convert_lits_ll_m N' M') = get_maximum_level M'\<close>
  unfolding get_maximum_level_def by auto

lemma refine_add_inv_in_set_with_arg:
  fixes f' :: \<open>'a \<Rightarrow> 'c nres\<close> and f :: \<open>'b \<Rightarrow> 'd nres\<close> and H' :: \<open>('c \<times> 'd) set\<close>
   assumes
    \<open>(f', f) \<in> R \<rightarrow> \<langle>{(T, T'). (T, T') \<in> H' \<and> P' T}\<rangle> nres_rel\<close>
   assumes
    \<open>(f, fg) \<in> R' \<rightarrow> \<langle>{(T, T'). (T, T') \<in> H'' \<and> Q T}\<rangle> nres_rel\<close> and
    \<open>\<And>x y. (x, y) \<in> R' \<Longrightarrow> nofail (fg y)\<close> and
    \<open>\<And>x y. (x,y) \<in> R \<Longrightarrow> \<exists>z. (y, z) \<in> R'\<close>
   shows
    \<open>(f', f) \<in> R \<rightarrow> \<langle>{(T, T'). (T, T') \<in> H' \<and> P' T \<and> Q T'}\<rangle> nres_rel\<close>
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
  by fastforce

lemma refine_add_inv_in_set_with_arg2:
  fixes f' :: \<open>'a \<Rightarrow> 'c nres\<close> and f :: \<open>'b \<Rightarrow> 'd nres\<close> and H' :: \<open>('c \<times> 'd) set\<close>
  assumes
    \<open>(f', f) \<in> R \<rightarrow> \<langle>{(T, T'). (T, T') \<in> H' \<and> P' T}\<rangle> nres_rel\<close>
  assumes
    \<open>\<And>x y. (x, y) \<in> R \<Longrightarrow> f y \<le> SPEC Q\<close>
  shows
    \<open>(f', f) \<in> R \<rightarrow> \<langle>{(T, T'). (T, T') \<in> H' \<and> P' T \<and> Q T'}\<rangle> nres_rel\<close>
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
  by fastforce

thm skip_and_resolve_loop_list_spec

(* TODO MOve *)
lemma nofail_skip_and_resolve_loop:
  assumes \<open>S' = twl_st_of S\<close> and
    \<open>twl_struct_invs (twl_st_of S)\<close> and
    \<open>twl_stgy_invs (twl_st_of S)\<close> and
    \<open>additional_WS_invs S\<close> and \<open>working_queue_list S = {#}\<close> and \<open>pending_list S = {#}\<close> and
    \<open>get_conflict (twl_st_of S)\<noteq> None\<close>
  shows \<open>nofail (skip_and_resolve_loop S')\<close>
  apply (rule SPEC_nofail)
  apply (rule skip_and_resolve_loop_spec)
  using assms by (auto simp add: pending_list_pending)
(* end move *)

lemma skip_and_resolve_loop_ll_spec:
  \<open>(skip_and_resolve_loop_ll, skip_and_resolve_loop_list) \<in>
  {(S, S'). (S, S') \<in> twl_st_of_ll \<and> twl_clause_of_ll_inv S \<and> twl_struct_invs (twl_st_of S') \<and> twl_stgy_invs (twl_st_of S') \<and>
  additional_WS_invs S'\<and> working_queue_ll S = {#} \<and> get_conflict_ll S \<noteq> None} \<rightarrow>
  \<langle>{(T, T'). (T, T') \<in> twl_st_of_ll \<and> twl_clause_of_ll_inv T \<and>
   additional_WS_invs T' \<and>
     twl_struct_invs (twl_st_of T') \<and>
     twl_stgy_invs (twl_st_of T') \<and>
     (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.skip
               (convert_to_state (twl_st_of T')) S') \<and>
     (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.resolve
               (convert_to_state (twl_st_of T')) S') \<and>
     pending (twl_st_of T') = {#} \<and>
     working_queue (twl_st_of T') = {#} \<and>
     get_conflict (twl_st_of T') \<noteq> None}\<rangle> nres_rel\<close>
  (is \<open>?S \<in> ?R \<rightarrow>  _\<close>)
proof -
  have get_conflict_ll_spec:
    \<open>((get_conflict_ll a = Some [], a), get_conflict_list a' = Some [], a') \<in>
    {((brk, S), (brk', S')). brk = brk' \<and> (S, S') \<in> twl_st_of_ll \<and> twl_clause_of_ll_inv S}\<close>
    if \<open>(a, a') \<in> twl_st_of_ll\<close> \<open>twl_clause_of_ll_inv a\<close>
    for a a'
    using that by (auto simp: get_conflict_ll_iff)
  have H: False if \<open>\<forall>i. Propagated L i = z \<and> D = N' ! i\<close> for L z D N'
  proof -
    have H: \<open>\<And>i. Propagated L i = z \<and> D = N' ! i\<close>
      using that by fast
    show False using H[of 0] H[of 1] by auto
  qed

  have R: \<open>?S \<in> ?R \<rightarrow>  \<langle>{(T, T'). (T, T') \<in> twl_st_of_ll \<and> twl_clause_of_ll_inv T}\<rangle> nres_rel\<close>
    unfolding skip_and_resolve_loop_ll_def skip_and_resolve_loop_list_def
    apply (refine_vcg get_conflict_ll_spec; remove_dummy_vars)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for S S' brk T brk' T'
      by (auto simp: is_decided_hg_get_trail_ll_iff skip_and_resolve_loop_inv_def)
    subgoal for S S' brk brk' M N U C NP UP WS Q M' N' U' C' NP' WS' Q'
      by (auto simp: twl_st_of_ll_def)
    subgoal for S S' brk brk' M N U C NP UP WS Q M' N' U' C' NP' WS' Q' L D
      by (cases M'; cases \<open>hd M'\<close>) (auto simp: twl_st_of_ll_def)
    subgoal for S S' brk brk' M N U C NP UP WS Q M' N' U' C' NP' WS' Q' L D L' D'
      by (cases C'; cases C) (auto simp: twl_st_of_ll_def)
    subgoal for S S' brk brk' M N U C NP UP WS Q M' N' U' C' NP' WS' Q' L D L' D'
      by (cases M') (auto simp: twl_st_of_ll_def twl_clause_of_ll_inv.simps)
    subgoal for S S' brk brk' M N U C NP UP WS Q M' N' U' C' NP' WS' Q' L D L' D'
      by (cases C'; cases C) (auto simp: twl_st_of_ll_def skip_and_resolve_loop_inv_def
          simp del: twl_clause_of_ll_inv.simps)
    subgoal for S S' brk brk' M N U C NP UP WS Q M' N' U' C' NP' WS' Q' L D L' D'
      by (cases M; cases C'; cases C) (auto simp: twl_st_of_ll_def skip_and_resolve_loop_inv_def map_tl
          resolve_cls_list_nil_iff simp del: twl_clause_of_ll_inv.simps dest!: H)
    subgoal for S S' brk brk' M N U C NP UP WS Q M' N' U' C' NP' WS' Q' L D L' D'
      by (cases C'; cases C) (auto simp: twl_st_of_ll_def skip_and_resolve_loop_inv_def map_tl
          resolve_cls_list_nil_iff simp del: twl_clause_of_ll_inv.simps)
    subgoal for S S' brk T brk' T'
      by auto
    done

  have help_auto: \<open>ba = {#}\<close> if \<open>twl_struct_invs (a, aa, ab, Some y, ad, t', t, ba)\<close>
    for a ba aa ab y ad t t'
    using that by (auto simp: twl_struct_invs_def)
  show ?thesis
    apply (rule refine_add_inv_in_set_with_arg[where fg = \<open>skip_and_resolve_loop\<close> and
          R' = \<open>{(S, S'). S' = twl_st_of S \<and> twl_struct_invs (twl_st_of S) \<and>
          twl_stgy_invs (twl_st_of S) \<and> additional_WS_invs S \<and> working_queue_list S = {#} \<and>
          pending_list S = {#} \<and> get_conflict (twl_st_of S) \<noteq> None}\<close> and
          H'' = \<open>{(T, T'). T' = twl_st_of T}\<close>])
    using R apply (simp; fail)
    using skip_and_resolve_loop_list_spec apply (simp add: weaken_SPEC; fail)
    apply (auto intro: nofail_skip_and_resolve_loop; fail)[]
    apply (auto simp: twl_st_of_ll_def map_option_case help_auto
        simp del: twl_clause_of_ll_inv.simps split: option.splits; fail)
    done
qed

definition backtrack_ll :: "'v twl_st_ll \<Rightarrow> 'v twl_st_ll nres" where
  \<open>backtrack_ll S\<^sub>0 =
    do {
      let (M, N, U, D, NP, WS, Q) = S\<^sub>0 in
      do {
        ASSERT(M \<noteq> []);
        L \<leftarrow> SPEC(\<lambda>L. L = lit_of (hd M));
        ASSERT(get_level M L = count_decided M);
        ASSERT(\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
         get_level M K = get_maximum_level M (mset (the D) - {#-L#}) + 1);
        M1 \<leftarrow> SPEC(\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (mset (the D) - {#-L#}) + 1);

        if length (the D) > 1
        then do {
          L' \<leftarrow> SPEC(\<lambda>L'. L' \<in># mset (the D) \<and>
            get_level M L' = get_maximum_level M (mset (the D) - {#-L#}));
          RETURN (Propagated (-L) (length N) # M1,
          N @ [[-L, L'] @ (remove1 (-L) (remove1 L' (the D)))], U,
            None, NP, WS, {#L#})
        }
        else do {
          RETURN (Propagated (-L) (length N) # M1, N @ [the D], U, None, NP, WS, {#L#})
        }
      }
    }
  \<close>

lemma get_all_ann_decomposition_convert_lits_ll_m:
  \<open>get_all_ann_decomposition (convert_lits_ll_m N M) =
  map (\<lambda>(a, b). (convert_lits_ll_m N a, convert_lits_ll_m N b)) (get_all_ann_decomposition M)\<close>
  apply (induction M rule: ann_lit_list_induct)
  subgoal by simp
  subgoal by (auto simp: map_tl)
  subgoal for L C M' by (cases \<open>get_all_ann_decomposition M'\<close>) auto
  done

lemma Some_eq_map_option_iff:
  \<open>Some y = map_option f da \<longleftrightarrow> (\<exists>da'. da = Some da' \<and> y = f da')\<close>
  by (cases da) auto
lemma Decided_convert_lit_ll_iff: \<open>Decided K = convert_lit_ll N z \<longleftrightarrow> z = Decided K\<close>
  by (cases z) auto

lemma backtrack_list_spec:
  \<open>(backtrack_ll, backtrack_list) \<in> {(S, S'). (S, S') \<in> twl_st_of_ll \<and>
        twl_clause_of_ll_inv S \<and> get_conflict_ll S \<noteq> None \<and> get_conflict_ll S \<noteq> Some [] \<and>
       working_queue_ll S = {#} \<and> pending_ll S = {#} \<and> additional_WS_invs S' \<and>
       no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of S')) \<and>
       no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of S')) \<and>
       twl_struct_invs (twl_st_of S') \<and> twl_stgy_invs (twl_st_of S')} \<rightarrow>
     \<langle>{(T, T'). (T, T') \<in> twl_st_of_ll \<and> twl_clause_of_ll_inv T \<and>
         additional_WS_invs T' \<and> get_conflict_list T' = None \<and> additional_WS_invs T' \<and>
       twl_struct_invs (twl_st_of T') \<and> twl_stgy_invs (twl_st_of T') \<and> working_queue_list T' = {#} \<and>
       pending_list T' \<noteq> {#}}\<rangle>nres_rel\<close>
  (is \<open>?bt \<in> ?R \<rightarrow> ?I\<close>)
proof -
  have decomp_spec: \<open>SPEC (\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
      get_level M K = get_maximum_level M (remove1_mset (- L) (mset (the D))) + 1)
     \<le> \<Down> {(M, M'). M' = convert_lits_ll_m N M}
        (SPEC (\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M') \<and>
           get_level M' K = get_maximum_level M'(remove1_mset (- L') (mset (the D'))) + 1))\<close>
    if \<open>(S, S') \<in> ?R\<close> --\<open>This unnecessary helps \<open>auto\<close> to take the correct \<open>S\<close>.\<close>
      \<open>M = get_trail_ll S\<close> \<open>M' = get_trail_list S'\<close> and \<open>N = get_clauses_ll S\<close>
      \<open>L = L'\<close> \<open>mset (the D) = mset (the D')\<close> \<open>(S, S') \<in> twl_st_of_ll\<close>
      for M M' L L' D D' N S S'
  proof (rule RES_refine)
    fix M1
    assume \<open>M1 \<in> {M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
      get_level M K = get_maximum_level M (remove1_mset (- L) (mset (the D))) + 1}\<close>
    then obtain K M2 where
      decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
      lev: \<open>get_level M K = get_maximum_level M (remove1_mset (- L) (mset (the D))) + 1\<close>
      by auto
    moreover have M': \<open>M' = convert_lits_ll_m N M\<close>
      using that by (auto simp: twl_st_of_ll_def get_all_ann_decomposition_convert_lits_ll_m)
    ultimately have
      \<open>(\<lambda>(a, b). (convert_lits_ll_m N a, convert_lits_ll_m N b)) (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M')\<close> and
      \<open>get_level M' K = get_maximum_level M' (remove1_mset (- L') (mset (the D'))) + 1\<close>
      unfolding get_all_ann_decomposition_convert_lits_ll_m M' that by force+
    then show \<open>\<exists>M1'\<in>{M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M') \<and>
      get_level M' K = get_maximum_level M' (remove1_mset (- L') (mset (the D'))) + 1}.
         (M1, M1') \<in> {(M, M'). M' = convert_lits_ll_m N M}\<close>
      by auto
  qed

  have R: \<open>?bt \<in> ?R \<rightarrow> \<langle>{(T, T'). (T, T') \<in> twl_st_of_ll \<and> twl_clause_of_ll_inv T}\<rangle>nres_rel\<close>
    unfolding backtrack_ll_def backtrack_list_def
    apply (refine_rcg decomp_spec; remove_dummy_vars)
    subgoal for M' N' U' D' NP' UP' WS' Q' M N U D NP WS Q
      by (auto simp: twl_st_of_ll_def)
    subgoal
      by (auto simp: twl_st_of_ll_def hd_map)
    subgoal for M' N' U' D' NP' UP' WS' Q' M N U D NP WS Q L L'
      by (auto simp add: twl_st_of_ll_def)
    subgoal premises H for M' N' U' D' NP' UP' WS' Q' M N U D NP WS Q L L'
    proof -
      have [simp]: \<open>M' = convert_lits_ll_m N M\<close>
        using H(1) by (auto simp add: twl_st_of_ll_def)[]
      have [simp]: \<open>mset (the D) = mset (the D')\<close>
        apply (cases D; cases D')
        using H(1) by (auto simp add: twl_st_of_ll_def)

      show \<open>\<exists>K M1 M2.
        (Decided K # M1, M2)
        \<in> set (get_all_ann_decomposition M) \<and>
        get_level M K =
        get_maximum_level M
        (remove1_mset (- L) (mset (the D))) +
        1\<close>
        using H(4-) by (fastforce simp add: get_all_ann_decomposition_convert_lits_ll_m
            Decided_convert_lit_ll_iff)[]
    qed
    subgoal
      by simp
    subgoal
      by simp
    subgoal
      by simp
    subgoal for M' N' U' D' NP' UP' WS' Q' M N U D NP WS Q L L'
      by (cases D; cases D') (auto simp: twl_st_of_ll_def)
    subgoal for M' N' U' D' NP' UP' WS' Q' M N U D NP WS Q L L'
      by auto
    subgoal for M' N' U' D' NP' UP' WS' Q' M N U D NP WS Q L L'
      by (cases D; cases D') (auto simp: twl_st_of_ll_def size_mset[symmetric] simp del: size_mset)
    subgoal for M' N' U' D' NP' UP' WS' Q' M N U D NP WS Q L L'
      by (rule SPEC_rule, cases D; cases D') (auto simp add: twl_st_of_ll_def)
    subgoal premises p for M' N' U' D' NP' UP' WS' Q' M N U D NP WS Q L L' M1 M1' K K'
    proof -
      thm p
      obtain M2 K'' where 
        \<open>(Decided K'' # M1, M2) \<in> set (get_all_ann_decomposition M)\<close>
        using p(12) by auto
      then obtain c where M: \<open>M = c @ M2 @ Decided K'' # M1\<close>
        by blast
      have K''K: \<open>((M, N, U, D, NP, WS, Q), M', N', U', D', NP', UP', WS', Q') \<in> twl_st_of_ll\<close> and
        ll_inv: \<open>twl_clause_of_ll_inv (M, N, U, D, NP, WS, Q)\<close>
        using p(1) by blast+
      have conv_N: \<open>convert_lit_ll (N @ xs) L = convert_lit_ll N L\<close> if \<open>L \<in> set M1\<close> for L xs
        using ll_inv that apply (cases L) by (auto simp: nth_append M twl_clause_of_ll_inv.simps)
      have conv_N: \<open>convert_lits_ll_m (N @ N') M1 = convert_lits_ll_m N M1\<close> for N'
        by (auto simp: conv_N)
      have \<open>((Propagated (- L) (length N) # M1, N @ [- L # K # remove1 (- L) (remove1 K (the D))], U,
          None, NP, WS, {#L#}),
        Propagated (- L') (- L' # K' # remove1 (- L') (remove1 K' (the D'))) # M1',
        N', add_mset (TWL_Clause [- L', K'] (remove1 (- L') (remove1 K' (the D')))) U',
          None, NP', UP', WS', {#L'#})
        \<in> twl_st_of_ll\<close>
        using p(2,3,4-6,16) K''K ll_inv unfolding M
        apply (cases M; cases M'; cases D; cases D')
          apply (auto simp add: twl_st_of_ll_def twl_clause_of_ll_inv.simps
            conv_N)
          (* apply (auto simp: twl_st_of_ll_def nth_append) *)
        sorry
      show ?thesis
        apply simp
        sorry
    qed
    subgoal
      sorry
    done

  show ?thesis
    apply (rule refine_add_inv_in_set_with_arg[OF R, where fg = \<open>backtrack\<close> and
       H'' = \<open>{(S, S'). S' = twl_st_of S}\<close> and
       R' = \<open> {(S, S'). S' = twl_st_of S \<and>
              (get_conflict_list S \<noteq> None) \<and>
              get_conflict_list S \<noteq> Some [] \<and>
              working_queue_list S = {#} \<and>
              pending_list S = {#} \<and>
              additional_WS_invs S \<and>
              (\<forall>a aa ab b. \<not> cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of S)) (a, aa, ab, b))
              \<and> (\<forall>a aa ab b. \<not> cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of S)) (a, aa, ab, b)) \<and> twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S)} \<close>])
    subgoal
      apply (rule mem_set_trans[OF _ backtrack_list_spec])
      apply (match_fun_rel; fast?)+
      done
    subgoal for S S'
      by (rule SPEC_nofail[OF backtrack_spec[of \<open>S'\<close>]])
         (auto simp: get_conflict_list_get_conflict pending_list_pending working_queu_empty_iff)
    subgoal for S S'
      by (cases S, cases S')
         (auto simp: get_conflict_list_get_conflict pending_list_pending working_queu_empty_iff
           twl_st_of_ll_def Some_eq_map_option_iff)
    done
qed

fun decide_list :: "'v twl_st_ll \<Rightarrow> 'v twl_st_ll nres"  where
  \<open>decide_ll (M, N, U, D, NP, UP, WS, Q) = do {
     L \<leftarrow> SPEC (\<lambda>L. undefined_lit M L \<and> atm_of L \<in> atms_of_mm (clause `# twl_clause_of `# N));
     RETURN (Decided L # M, N, U, D, NP, UP, WS, {#-L#})
  }
\<close>

definition cdcl_twl_o_prog_ll :: "'v twl_st_ll \<Rightarrow> (bool \<times> 'v twl_st_ll) nres"  where
  \<open>cdcl_twl_o_prog_ll S =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S in
      do {
        if D = None
        then
          if (\<exists>L. undefined_lit M L \<and> atm_of L \<in> atms_of_mm (clause `# twl_clause_of `# N))
          then do {S \<leftarrow> decide_ll S; RETURN (False, S)}
          else do {RETURN (True, S)}
        else do {
          T \<leftarrow> skip_and_resolve_loop_ll S;
          if get_conflict_list T \<noteq> Some []
          then do {U \<leftarrow> backtrack_ll T; RETURN (False, U)}
          else do {RETURN (True, T)}
        }
      }
    }
  \<close>
end