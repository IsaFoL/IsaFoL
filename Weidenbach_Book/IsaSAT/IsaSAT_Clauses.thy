theory IsaSAT_Clauses
  imports IsaSAT_Arena
begin

(* TODO This file should probably be merged with IsaSAT_Arena*)

chapter \<open>The memory representation: Manipulation of all clauses\<close>

subsubsection \<open>Representation of Clauses\<close>

(* TODO kill *)
named_theorems isasat_codegen \<open>lemmas that should be unfolded to generate (efficient) code\<close>

type_synonym clause_annot = \<open>clause_status \<times> nat \<times> nat\<close>

type_synonym clause_annots = \<open>clause_annot list\<close>


definition list_fmap_rel :: \<open>_ \<Rightarrow> (arena \<times> nat clauses_l) set\<close> where
  \<open>list_fmap_rel vdom = {(arena, N). valid_arena arena N vdom}\<close>

lemma nth_clauses_l:
  \<open>(uncurry2 (RETURN ooo (\<lambda>N i j. arena_lit N (i+j))),
      uncurry2 (RETURN ooo (\<lambda>N i j. N \<propto> i ! j)))
    \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>f
      list_fmap_rel vdom \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: list_fmap_rel_def arena_lifting)

abbreviation clauses_l_fmat where
  \<open>clauses_l_fmat \<equiv> list_fmap_rel\<close>

type_synonym vdom = \<open>nat set\<close>

definition fmap_rll :: \<open>(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal\<close> where
  [simp]: \<open>fmap_rll l i j = l \<propto> i ! j\<close>

definition fmap_rll_u :: \<open>(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal\<close> where
  [simp]: \<open>fmap_rll_u  = fmap_rll\<close>

definition fmap_rll_u64 :: \<open>(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal\<close> where
  [simp]: \<open>fmap_rll_u64  = fmap_rll\<close>


definition fmap_length_rll_u :: \<open>(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>fmap_length_rll_u l i = length_uint32_nat (l \<propto> i)\<close>

declare fmap_length_rll_u_def[symmetric, isasat_codegen]
definition fmap_length_rll_u64 :: \<open>(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>fmap_length_rll_u64 l i = length_uint32_nat (l \<propto> i)\<close>


declare fmap_length_rll_u_def[symmetric, isasat_codegen]


definition fmap_length_rll :: \<open>(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat\<close> where
  [simp]: \<open>fmap_length_rll l i = length (l \<propto> i)\<close>

definition fmap_swap_ll where
  [simp]: \<open>fmap_swap_ll N i j f = (N(i \<hookrightarrow> swap (N \<propto> i) j f))\<close>

text \<open>From a performance point of view, appending several time a single element is less efficient
than reserving a space that is large enough directly. However, in this case the list of clauses \<^term>\<open>N\<close>
is so large that there should not be any difference\<close>
definition fm_add_new where
 \<open>fm_add_new b C N0 = do {
    let s = length C - 2;
    let lbd = shorten_lbd s;
    let st = (if b then AStatus IRRED 0 lbd else AStatus LEARNED 0 lbd);
    let l = length N0;
    let N = (if is_short_clause C then
          (((N0 @ [st]))) @ [ASize s]
          else ((((N0 @ [APos 0]) @ [st]))) @ [ASize (s)]);
    (i, N) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(i, N). i < length C \<longrightarrow> length N < header_size C + length N0 + length C\<^esup>
      (\<lambda>(i, N). i < length C)
      (\<lambda>(i, N). do {
        ASSERT(i < length C);
        RETURN (i+1, N @ [ALit (C ! i)])
      })
      (0, N);
    RETURN (N, l + header_size C)
  }\<close>

lemma nth_append_clause:
  \<open>a < length C \<Longrightarrow> append_clause b C N ! (length N + header_size C + a) = ALit (C ! a)\<close>
  unfolding append_clause_def header_size_Suc_def append_clause_skeleton_def
  by (auto simp: nth_Cons nth_append)

lemma fm_add_new_append_clause:
  \<open>fm_add_new b C N \<le> RETURN (append_clause b C N, length N + header_size C)\<close>
  unfolding fm_add_new_def
  apply (rewrite at \<open>let _ = length _ in _\<close> Let_def)
  apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(i, _). Suc (length C) - i)\<close> and
    I' = \<open>\<lambda>(i, N'). N' = take (length N + header_size C + i) (append_clause b C N) \<and>
      i \<le> length C\<close>])
  subgoal by auto
  subgoal by (auto simp: append_clause_def header_size_def
    append_clause_skeleton_def split: if_splits)
  subgoal by (auto simp: append_clause_def header_size_def
    append_clause_skeleton_def split: if_splits)
  subgoal by simp
  subgoal by simp
  subgoal by auto
  subgoal by (auto simp: take_Suc_conv_app_nth nth_append_clause)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

definition fm_add_new_at_position
   :: \<open>bool \<Rightarrow> nat \<Rightarrow> 'v clause_l \<Rightarrow> 'v clauses_l \<Rightarrow> 'v clauses_l\<close>
where
  \<open>fm_add_new_at_position b i C N = fmupd i (C, b) N\<close>

definition AStatus_IRRED where
  \<open>AStatus_IRRED = AStatus IRRED 0\<close>

definition AStatus_IRRED2 where
  \<open>AStatus_IRRED2 = AStatus IRRED 1\<close>

definition AStatus_LEARNED where
  \<open>AStatus_LEARNED = AStatus LEARNED 1\<close>


definition AStatus_LEARNED2 where
  \<open>AStatus_LEARNED2 = AStatus LEARNED 0\<close>


definition (in -)fm_add_new_fast where
 [simp]: \<open>fm_add_new_fast = fm_add_new\<close>

lemma (in -)append_and_length_code_fast:
  \<open>length ba \<le> Suc (Suc uint32_max) \<Longrightarrow>
       2 \<le> length ba \<Longrightarrow>
       length b \<le> uint64_max - (uint32_max + 5) \<Longrightarrow>
       (aa, header_size ba) \<in> uint64_nat_rel \<Longrightarrow>
       (ab, length b) \<in> uint64_nat_rel \<Longrightarrow>
       length b + header_size ba \<le> uint64_max\<close>
  by (auto simp: uint64_max_def uint32_max_def header_size_def)



definition (in -)four_uint64_nat where
  [simp]: \<open>four_uint64_nat = (4 :: nat)\<close>
definition (in -)five_uint64_nat where
  [simp]: \<open>five_uint64_nat = (5 :: nat)\<close>

definition append_and_length_fast_code_pre where
  \<open>append_and_length_fast_code_pre \<equiv> \<lambda>((b, C), N). length C \<le> uint32_max+2 \<and> length C \<ge> 2 \<and>
          length N + length C + MAX_HEADER_SIZE \<le> sint64_max\<close>


lemma fm_add_new_alt_def:
 \<open>fm_add_new b C N0 = do {
      let s = length C - 2;
      let lbd = shorten_lbd s;
      let st = (if b then AStatus_IRRED lbd else AStatus_LEARNED2 lbd);
      let l = length N0;
      let N =
        (if is_short_clause C
          then ((N0 @ [st])) @
              [ASize s]
          else (((N0 @ [APos 0]) @ [st])) @
              [ASize s]);
      (i, N) \<leftarrow>
        WHILE\<^sub>T\<^bsup> \<lambda>(i, N). i < length C \<longrightarrow> length N < header_size C + length N0 + length C\<^esup>
          (\<lambda>(i, N). i < length C)
          (\<lambda>(i, N). do {
                _ \<leftarrow> ASSERT (i < length C);
                RETURN (i + 1, N @ [ALit (C ! i)])
              })
          (0, N);
      RETURN (N, l + header_size C)
    }\<close>
  unfolding fm_add_new_def Let_def AStatus_LEARNED2_def AStatus_IRRED2_def
     AStatus_LEARNED_def AStatus_IRRED_def
  by auto

definition fmap_swap_ll_u64 where
  [simp]: \<open>fmap_swap_ll_u64 = fmap_swap_ll\<close>

definition fm_mv_clause_to_new_arena where
 \<open>fm_mv_clause_to_new_arena C old_arena new_arena0 = do {
    ASSERT(arena_is_valid_clause_idx old_arena C);
    ASSERT(C \<ge> (if  (arena_length old_arena C) \<le> 4 then MIN_HEADER_SIZE else MAX_HEADER_SIZE));
    let st = C - (if  (arena_length old_arena C) \<le> 4 then MIN_HEADER_SIZE else MAX_HEADER_SIZE);
    ASSERT(C +  (arena_length old_arena C) \<le> length old_arena);
    let en = C +  (arena_length old_arena C);
    (i, new_arena) \<leftarrow>
        WHILE\<^sub>T\<^bsup> \<lambda>(i, new_arena). i < en \<longrightarrow> length new_arena < length new_arena0 + (arena_length old_arena C) + (if  (arena_length old_arena C) \<le> 4 then MIN_HEADER_SIZE else MAX_HEADER_SIZE) \<^esup>
          (\<lambda>(i, new_arena). i < en)
          (\<lambda>(i, new_arena). do {
              ASSERT (i < length old_arena \<and> i < en);
              RETURN (i + 1, new_arena @ [old_arena ! i])
          })
          (st, new_arena0);
      RETURN (new_arena)
  }\<close>

lemma valid_arena_append_clause_slice:
  assumes
    \<open>valid_arena old_arena N vd\<close> and
    \<open>valid_arena new_arena N' vd'\<close> and
    \<open>C \<in># dom_m N\<close>
  shows \<open>valid_arena (new_arena @ clause_slice old_arena N C)
    (fmupd (length new_arena + header_size (N \<propto> C)) (N \<propto> C, irred N C) N')
    (insert (length new_arena + header_size (N \<propto> C)) vd')\<close>
proof -
  define pos st lbd used where
    \<open>pos = (if is_long_clause (N \<propto> C) then arena_pos old_arena C - 2 else 0)\<close> and
    \<open>st = arena_status old_arena C\<close> and
    \<open>lbd = arena_lbd old_arena C\<close> and
    \<open>used = arena_used old_arena C\<close>
  have \<open>2 \<le> length (N \<propto> C)\<close>
    unfolding st_def used_def lbd_def
      append_clause_skeleton_def arena_status_def
      xarena_status_def arena_used_def
      xarena_used_def
      arena_lbd_def xarena_lbd_def
    using arena_lifting[OF assms(1,3)]
    by (auto simp: is_Status_def is_Pos_def is_Size_def)
  have
    45: \<open>4 = (Suc (Suc (Suc (Suc 0))))\<close>
     \<open>5 = Suc (Suc (Suc (Suc (Suc 0))))\<close>
     \<open>3 = (Suc (Suc (Suc 0)))\<close>
     \<open>2 = (Suc (Suc 0))\<close>
    by auto
  have sl: \<open>clause_slice old_arena N C =
     (if is_long_clause (N \<propto> C) then [APos pos]
     else []) @
     [AStatus st used lbd, ASize (length (N \<propto> C) - 2)] @
     map ALit (N \<propto> C)\<close>
    unfolding st_def used_def lbd_def
      append_clause_skeleton_def arena_status_def
      xarena_status_def arena_used_def
      xarena_used_def
      pos_def arena_pos_def
      xarena_pos_def
      arena_lbd_def xarena_lbd_def
      arena_length_def xarena_length_def
    using arena_lifting[OF assms(1,3)]
    by (auto simp: is_Status_def is_Pos_def is_Size_def
      header_size_def 45
      slice_Suc_nth[of \<open>C - Suc (Suc (Suc (Suc 0)))\<close>]
      slice_Suc_nth[of \<open>C - Suc (Suc (Suc 0))\<close>]
      slice_Suc_nth[of \<open>C - Suc (Suc 0)\<close>]
      slice_Suc_nth[of \<open>C - Suc 0\<close>]
      SHIFTS_alt_def arena_length_def
      arena_pos_def xarena_pos_def
      arena_status_def xarena_status_def)

  have \<open>2 \<le> length (N \<propto> C)\<close> and
    \<open>pos \<le> length (N \<propto> C) - 2\<close> and
    \<open>st = IRRED \<longleftrightarrow> irred N C\<close> and
    \<open>st \<noteq> DELETED\<close>
    unfolding st_def used_def lbd_def pos_def
      append_clause_skeleton_def st_def
    using arena_lifting[OF assms(1,3)]
    by (cases \<open>is_short_clause (N \<propto> C)\<close>;
      auto split: arena_el.splits if_splits
        simp: header_size_def arena_pos_def; fail)+

  then have \<open>valid_arena (append_clause_skeleton pos st used lbd (N \<propto> C) new_arena)
    (fmupd (length new_arena + header_size (N \<propto> C)) (N \<propto> C, irred N C) N')
    (insert (length new_arena + header_size (N \<propto> C)) vd')\<close>
    apply -
    by (rule valid_arena_append_clause_skeleton[OF assms(2), of \<open>N \<propto> C\<close> _ st
      pos used lbd]) auto
  moreover have
    \<open>append_clause_skeleton pos st used lbd (N \<propto> C) new_arena =
      new_arena @ clause_slice old_arena N C\<close>
    by (auto simp: append_clause_skeleton_def sl)
  ultimately show ?thesis
    by auto
qed

lemma fm_mv_clause_to_new_arena:
  assumes \<open>valid_arena old_arena N vd\<close> and
    \<open>valid_arena new_arena N' vd'\<close> and
    \<open>C \<in># dom_m N\<close>
  shows \<open>fm_mv_clause_to_new_arena C old_arena new_arena \<le>
    SPEC(\<lambda>new_arena'.
      new_arena' = new_arena @ clause_slice old_arena N C \<and>
      valid_arena (new_arena @ clause_slice old_arena N C)
        (fmupd (length new_arena + header_size (N \<propto> C)) (N \<propto> C, irred N C) N')
        (insert (length new_arena + header_size (N \<propto> C)) vd'))\<close>
proof -
  define st and en where
    \<open>st = C - (if arena_length old_arena C \<le> 4 then MIN_HEADER_SIZE else MAX_HEADER_SIZE)\<close> and
    \<open>en = C + arena_length old_arena C\<close>
  have st:
    \<open>st = C - header_size (N \<propto> C)\<close>
    using assms
    unfolding st_def
    by (auto simp: st_def header_size_def
        arena_lifting)
  show ?thesis
    using assms
    unfolding fm_mv_clause_to_new_arena_def st_def[symmetric]
      en_def[symmetric] Let_def
    apply (refine_vcg
     WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(i, N). en - i)\<close> and
       I' = \<open>\<lambda>(i, new_arena'). i \<le> C + length (N\<propto>C) \<and> i \<ge> st \<and>
         new_arena' = new_arena @
	   Misc.slice (C - header_size (N\<propto>C)) i old_arena\<close>])
    subgoal
      unfolding arena_is_valid_clause_idx_def
      by auto
    subgoal using arena_lifting(4)[OF assms(1)] by (auto
        dest!: arena_lifting(1)[of _ N _ C] simp: header_size_def split: if_splits)
    subgoal using arena_lifting(10, 4) en_def by auto
    subgoal
      by auto
    subgoal by auto
    subgoal
      using arena_lifting[OF assms(1,3)]
      by (auto simp: st)
    subgoal
      by (auto simp: st arena_lifting)
    subgoal
      using arena_lifting[OF assms(1,3)]
      by (auto simp: st en_def)
    subgoal
      using arena_lifting[OF assms(1,3)]
      by (auto simp: st en_def)
    subgoal by auto
    subgoal using arena_lifting[OF assms(1,3)]
        by (auto simp: slice_len_min_If en_def st_def header_size_def)
    subgoal
      using arena_lifting[OF assms(1,3)]
      by (auto simp: st en_def)
    subgoal
      using arena_lifting[OF assms(1,3)]
      by (auto simp: st)
    subgoal
      by (auto simp: st en_def arena_lifting[OF assms(1,3)]
        slice_append_nth)
    subgoal by auto
    subgoal by (auto simp: en_def arena_lifting)
    subgoal
      using valid_arena_append_clause_slice[OF assms]
      by auto
    done
qed

lemma size_learned_clss_dom_m: \<open>size (learned_clss_l N) \<le> size (dom_m N)\<close>
  unfolding ran_m_def
  apply (rule order_trans[OF size_filter_mset_lesseq])
  by (auto simp: ran_m_def)


lemma valid_arena_ge_length_clauses:
  assumes \<open>valid_arena arena N vdom\<close>
  shows \<open>length arena \<ge> (\<Sum>C \<in># dom_m N. length (N \<propto> C) + header_size (N \<propto> C))\<close>
proof -
  obtain xs where
    mset_xs: \<open>mset xs = dom_m N\<close> and sorted: \<open>sorted xs\<close> and dist[simp]: \<open>distinct xs\<close> and set_xs: \<open>set xs = set_mset (dom_m N)\<close>
    using distinct_mset_dom distinct_mset_mset_distinct mset_sorted_list_of_multiset by fastforce
  then have 1: \<open>set_mset (mset xs) = set xs\<close> by (meson set_mset_mset)

  have diff: \<open>xs \<noteq> [] \<Longrightarrow> a \<in> set xs \<Longrightarrow> a < last xs \<Longrightarrow> a + length (N \<propto> a) \<le> last xs\<close>  for a
     using valid_minimal_difference_between_valid_index[OF assms, of a \<open>last xs\<close>]
     mset_xs[symmetric] sorted  by (cases xs rule: rev_cases; auto simp: sorted_append)
  have \<open>set xs \<subseteq> set_mset (dom_m N)\<close>
     using mset_xs[symmetric] by auto
  then have \<open>(\<Sum>A\<in>set xs. length (N \<propto> A) + header_size (N \<propto> A)) \<le> Max (insert 0 ((\<lambda>A. A + length (N \<propto> A)) ` (set xs)))\<close>
    (is \<open>?P xs \<le> ?Q xs\<close>)
     using sorted dist
  proof (induction xs rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc x xs)
    then have IH: \<open>(\<Sum>A\<in>set xs. length (N \<propto> A) + header_size (N \<propto> A))
    \<le> Max (insert 0 ((\<lambda>A. A + length (N \<propto> A)) ` set xs))\<close> and
      x_dom: \<open>x \<in># dom_m N\<close> and
      x_max: \<open>\<And>a. a \<in> set xs \<Longrightarrow> x > a\<close> and
      xs_N: \<open>set xs \<subseteq> set_mset (dom_m N)\<close>
         apply (clarsimp_all simp: sorted_append order.order_iff_strict sorted_wrt_append)
      apply (metis (full_types) insert_subset order_less_le subsetI)
      apply (metis (full_types) insert_subset order_less_le subsetI)
      apply (meson distinct_sorted_append snoc.prems(2) snoc.prems(3))
      apply blast
      done
    have x_ge: \<open>header_size (N \<propto> x) \<le> x\<close>
      using assms \<open>x \<in># dom_m N\<close> arena_lifting(1) by blast
    have diff: \<open>a \<in> set xs \<Longrightarrow> a + length (N \<propto> a) + header_size (N \<propto> x) \<le> x\<close>
       \<open>a \<in> set xs \<Longrightarrow> a + length (N \<propto> a) \<le> x\<close>  for a
      using valid_minimal_difference_between_valid_index[OF assms, of a x]
      x_max[of a] xs_N x_dom by auto

    have \<open>?P (xs @ [x]) \<le> ?P xs + length (N \<propto> x) + header_size (N \<propto> x)\<close>
      using snoc by auto
    also have \<open>... \<le> ?Q xs + (length (N \<propto> x) + header_size (N \<propto> x))\<close>
      using IH by auto
    also have \<open>... \<le> (length (N \<propto> x) + x)\<close>
      by (subst linordered_ab_semigroup_add_class.Max_add_commute2[symmetric]; auto intro: diff x_ge)
    also have \<open>... = Max (insert (x + length (N \<propto> x)) ((\<lambda>x. x + length (N \<propto> x)) ` set xs))\<close>
      by (subst eq_commute)
        (auto intro!: linorder_class.Max_eqI intro: order_trans[OF diff(2)])
    finally show ?case by auto
  qed
  also have \<open>... \<le> (if xs = [] then 0 else last xs + length (N \<propto> last xs))\<close>
   using sorted distinct_sorted_append[of \<open>butlast xs\<close> \<open>last xs\<close>] dist
   by (cases \<open>xs\<close> rule: rev_cases)
     (auto intro: order_trans[OF diff])
  also have \<open>... \<le> length arena\<close>
   using arena_lifting(7)[OF assms, of \<open>last xs\<close> \<open>length (N \<propto> last xs) - 1\<close>] mset_xs[symmetric] assms
   by (cases \<open>xs\<close> rule: rev_cases) (auto simp: arena_lifting)
  finally show ?thesis
    unfolding mset_xs[symmetric]
    by (subst distinct_sum_mset_sum) auto
qed

lemma valid_arena_size_dom_m_le_arena: \<open>valid_arena arena N vdom \<Longrightarrow> size (dom_m N) \<le> length arena\<close>
  using valid_arena_ge_length_clauses[of arena N vdom]
  ordered_comm_monoid_add_class.sum_mset_mono[of \<open>dom_m N\<close> \<open>\<lambda>_. 1\<close>
    \<open>\<lambda>C. length (N \<propto> C) + header_size (N \<propto> C)\<close>]
  by (fastforce simp: header_size_def split: if_splits)

(*TODE Move*)
section \<open>Virtual domain\<close>

text \<open>The virtual domain is composed of the addressable (and accessible) elements, i.e.,
  the domain and all the deleted clauses that are still present in the watch lists.
\<close>
definition vdom_m :: \<open>nat multiset \<Rightarrow> (nat literal \<Rightarrow> (nat \<times> _) list) \<Rightarrow> (nat, 'b) fmap \<Rightarrow> nat set\<close> where
  \<open>vdom_m \<A> W N = \<Union>(((`) fst) ` set ` W ` set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)) \<union> set_mset (dom_m N)\<close>

lemma vdom_m_simps[simp]:
  \<open>bh \<in># dom_m N \<Longrightarrow> vdom_m \<A> W (N(bh \<hookrightarrow> C)) = vdom_m \<A> W N\<close>
  \<open>bh \<notin># dom_m N \<Longrightarrow> vdom_m \<A> W (N(bh \<hookrightarrow> C)) = insert bh (vdom_m \<A> W N)\<close>
  by (force simp: vdom_m_def split: if_splits)+

lemma vdom_m_simps2[simp]:
  \<open>i \<in># dom_m N \<Longrightarrow> vdom_m \<A> (W(L := W L @ [(i, C)])) N = vdom_m \<A> W N\<close>
  \<open>bi \<in># dom_m ax \<Longrightarrow> vdom_m \<A> (bp(L:= bp L @ [(bi, av')])) ax = vdom_m \<A> bp ax\<close>
  by (force simp: vdom_m_def split: if_splits)+

lemma vdom_m_simps3[simp]:
  \<open>fst biav' \<in># dom_m ax \<Longrightarrow> vdom_m \<A> (bp(L:= bp L @ [biav'])) ax = vdom_m \<A> bp ax\<close>
  by (cases biav'; auto simp: dest: multi_member_split[of L] split: if_splits)

text \<open>What is the difference with the next lemma?\<close>
lemma [simp]:
  \<open>bf \<in># dom_m ax \<Longrightarrow> vdom_m \<A> bj (ax(bf \<hookrightarrow> C')) = vdom_m \<A> bj (ax)\<close>
  by (force simp: vdom_m_def split: if_splits)+

lemma vdom_m_simps4[simp]:
  \<open>i \<in># dom_m N \<Longrightarrow>
     vdom_m \<A> (W (L1 := W L1 @ [(i, C1)], L2 := W L2 @ [(i, C2)])) N = vdom_m \<A> W N\<close>
 by (auto simp: vdom_m_def image_iff dest: multi_member_split split: if_splits)

text \<open>This is @{thm vdom_m_simps4} if the assumption of distinctness is not present in the context.\<close>
lemma vdom_m_simps4'[simp]:
  \<open>i \<in># dom_m N \<Longrightarrow>
     vdom_m \<A> (W (L1 := W L1 @ [(i, C1), (i, C2)])) N = vdom_m \<A> W N\<close>
  by (auto simp: vdom_m_def image_iff dest: multi_member_split split: if_splits)

text \<open>We add a spurious dependency to the parameter of the locale:\<close>
definition empty_watched :: \<open>nat multiset \<Rightarrow> nat literal \<Rightarrow> (nat \<times> nat literal \<times> bool) list\<close> where
  \<open>empty_watched \<A> = (\<lambda>_. [])\<close>

lemma vdom_m_empty_watched[simp]:
  \<open>vdom_m \<A> (empty_watched \<A>') N = set_mset (dom_m N)\<close>
  by (auto simp: vdom_m_def empty_watched_def)

text \<open>The following rule makes the previous one not applicable. Therefore, we do not mark this lemma as
simp.\<close>
lemma vdom_m_simps5:
  \<open>i \<notin># dom_m N \<Longrightarrow> vdom_m \<A> W (fmupd i C N) = insert i (vdom_m \<A> W N)\<close>
  by (force simp: vdom_m_def image_iff dest: multi_member_split split: if_splits)

lemma in_watch_list_in_vdom:
  assumes \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and \<open>w < length (watched_by S L)\<close>
  shows \<open>fst (watched_by S L ! w) \<in> vdom_m \<A> (get_watched_wl S) (get_clauses_wl S)\<close>
  using assms
  unfolding vdom_m_def
  by (cases S) (auto dest: multi_member_split)

lemma in_watch_list_in_vdom':
  assumes \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and \<open>A \<in> set (watched_by S L)\<close>
  shows \<open>fst A \<in> vdom_m \<A> (get_watched_wl S) (get_clauses_wl S)\<close>
  using assms
  unfolding vdom_m_def
  by (cases S) (auto dest: multi_member_split)

lemma in_dom_in_vdom[simp]:
  \<open>x \<in># dom_m N \<Longrightarrow> x \<in> vdom_m \<A> W N\<close>
  unfolding vdom_m_def
  by (auto dest: multi_member_split)

lemma in_vdom_m_upd:
  \<open>x1f \<in> vdom_m \<A> (g(x1e := (g x1e)[x2 := (x1f, x2f)])) b\<close>
  if \<open>x2 < length (g x1e)\<close> and \<open>x1e \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
  using that
  unfolding vdom_m_def
  by (auto dest!: multi_member_split intro!: set_update_memI img_fst)


lemma in_vdom_m_fmdropD:
  \<open>x \<in> vdom_m \<A> ga (fmdrop C baa) \<Longrightarrow> x \<in> (vdom_m \<A> ga baa)\<close>
  unfolding vdom_m_def
  by (auto dest: in_diffD)

end
