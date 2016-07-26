(*  Title: CDCL with Two Watched Literals
    Author: Jasmin Blanchette <jasmin.blanchette@inria.fr>
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

section \<open>2-Watched-Literal\<close>

theory CDCL_Two_Watched_Literals
imports CDCL_W_Abstract_State
begin

subsubsection \<open>Two-watched literals\<close>
datatype 'v twl_clause =
  TWL_Clause (watched: 'v) (unwatched: 'v)

text \<open>The structural invariants states that there are at most two watched elements, that the watched
  literals are distinct, and that there are 2 watched literals if there are at least than two
  different literals in the full clauses.\<close>
primrec struct_wf_twl_cls :: "'v multiset twl_clause \<Rightarrow> bool" where
"struct_wf_twl_cls (TWL_Clause W UW) \<longleftrightarrow>
   size W \<le> 2 \<and> (size W < 2 \<longrightarrow> UW \<subseteq># W) \<and> distinct_mset (W + UW)"

fun clause :: "'a twl_clause \<Rightarrow> 'a :: {plus}"  where
"clause (TWL_Clause W UW) = W + UW"

primrec (nonexhaustive) index :: "'a list \<Rightarrow>'a \<Rightarrow> nat" where
"index (a # l) c = (if a = c then 0 else 1+index l c)"

lemma index_nth:
  "a \<in> set l \<Longrightarrow> l ! (index l a) = a"
  by (induction l) auto

definition defined_before :: "('a, 'b) ann_lit list \<Rightarrow> 'a literal \<Rightarrow> 'a literal \<Rightarrow> bool" where
"defined_before M L L' \<equiv> index (map lit_of M) L' \<le> index (map lit_of M) L"

lemma defined_before_tl:
  assumes
    L: "L' \<in> lits_of_l M" and
    L_hd: "L \<noteq> hd (map lit_of M)" and
    L'_hd: "L' \<noteq> hd (map lit_of M)" and
    def_M: "defined_before M L L'"
  shows "defined_before (tl M) L L'"
  using L_hd L'_hd def_M  unfolding defined_before_def by (cases M) auto

text \<open>We need the following property about updates: if there is a literal @{term L} with
  @{term "-L"} in the trail, and @{term L} is not  watched, then it stays unwatched; i.e., while
  updating with @{term rewatch}, @{term L} does not get swapped with a watched literal @{term L'}
  such that @{term "-L'"} is in the trail. This corresponds to the laziness of the data structure.

  Remark that @{term M} is a trail: literals at the end were the first to be added to the trail.\<close>
primrec watched_only_lazy_updates :: "('v, 'mark) ann_lits \<Rightarrow>
  'v literal multiset twl_clause \<Rightarrow> bool" where
"watched_only_lazy_updates M (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L'\<in># W. \<forall>L \<in># UW.
    -L' \<in> lits_of_l M \<longrightarrow> -L \<in> lits_of_l M \<longrightarrow> L \<notin># W \<longrightarrow>
      defined_before M (-L) (-L'))"

primrec watched_wf_twl_cls_decision where
"watched_wf_twl_cls_decision M (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L \<in># W. -L \<in> lits_of_l M \<longrightarrow> remove1_mset L W \<subseteq># image_mset lit_of (mset M) \<longrightarrow>
    (\<forall>L' \<in># W. L \<noteq> L' \<longrightarrow> defined_before M L' (-L)))"

primrec watched_wf_twl_cls_no_decision where
"watched_wf_twl_cls_no_decision M (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L \<in># W. -L \<in> lits_of_l M \<longrightarrow> \<not>remove1_mset L W \<subseteq># image_mset lit_of (mset M) \<longrightarrow>
    (\<forall>L' \<in># UW. L' \<notin># W \<longrightarrow> -L' \<in> lits_of_l M))"


text \<open>If the negation of a watched literal is included in the trail, then the negation of
  every unwatched literals is also included in the trail. Otherwise, the data-structure has to be
  updated.\<close>
fun watched_wf_twl_cls :: "('a, 'b) ann_lits \<Rightarrow> 'a literal multiset twl_clause \<Rightarrow>
  bool" where
"watched_wf_twl_cls M C \<longleftrightarrow>
   watched_wf_twl_cls_no_decision M C \<and> watched_wf_twl_cls_decision M C"

lemma watched_wf_twl_cls_single_Ball:
  "watched_wf_twl_cls M (TWL_Clause W UW) =
    (\<forall>L \<in># W. -L \<in> lits_of_l M \<longrightarrow>
      ((remove1_mset L W \<subseteq># image_mset lit_of (mset M) \<longrightarrow>
        (\<forall>L' \<in># W. L \<noteq> L' \<longrightarrow> defined_before M L' (-L))) \<and>
      (\<not>remove1_mset L W \<subseteq># image_mset lit_of (mset M) \<longrightarrow>
        (\<forall>L' \<in># UW. L' \<notin># W \<longrightarrow> -L' \<in> lits_of_l M))))"
  unfolding watched_wf_twl_cls.simps watched_wf_twl_cls_no_decision.simps
  watched_wf_twl_cls_decision.simps by blast

text \<open>Here are the invariant strictly related to the 2-WL data structure.\<close>
primrec wf_twl_cls :: "('v, 'mark) ann_lits \<Rightarrow> 'v literal multiset twl_clause \<Rightarrow> bool" where
  "wf_twl_cls M (TWL_Clause W UW) \<longleftrightarrow>
   struct_wf_twl_cls (TWL_Clause W UW) \<and>
   watched_wf_twl_cls M (TWL_Clause W UW) \<and>
   watched_only_lazy_updates M (TWL_Clause W UW)"

lemma wf_twl_cls_annotation_independant:
  assumes M: "map lit_of M = map lit_of M'"
  shows "wf_twl_cls M (TWL_Clause W UW) \<longleftrightarrow> wf_twl_cls M' (TWL_Clause W UW)"
proof -
  have "lits_of_l M = lits_of_l M'"
    using arg_cong[OF M, of set] by (simp add: lits_of_def)
  moreover have "image_mset lit_of (mset M) = image_mset lit_of (mset M')"
    by (metis M mset_map)
  moreover have "defined_before M = defined_before M'"
    by (intro ext) (auto simp: defined_before_def M)
  ultimately show ?thesis
    by auto
qed

lemma less_eq_2_iff_eq_2_less_eq_Suc_1: "a \<le> 2 \<longleftrightarrow> a = 2 \<or> a \<le> Suc 0"
  by linarith

lemma remove_1_mset_single_add_if:
  "remove1_mset K ({#L#} + xs) = (if K = L then xs else {#L#} + remove1_mset K xs)"
  by (auto simp: multiset_eq_iff)

lemma remove_1_mset_single_if:
  "remove1_mset K {#L#} = (if K = L then {#} else {#L#})"
  by (auto simp: multiset_eq_iff)

lemma wf_twl_cls_wf_twl_cls_tl:
  fixes C :: "'v clause twl_clause"
  assumes wf: "wf_twl_cls M C" and n_d: "no_dup M"
  shows "wf_twl_cls (tl M) C"
proof (cases M)
  case Nil
  then show ?thesis using wf
    by (cases C) (simp add: wf_twl_cls.simps[of "tl _"])
next
  case (Cons l M') note M = this(1)
  obtain W UW where C: "C = TWL_Clause W UW"
    by (cases C)
  show ?thesis
    unfolding C wf_twl_cls.simps
    proof (intro conjI)
      show struct_wf: "struct_wf_twl_cls (TWL_Clause W UW)"
        using wf unfolding C wf_twl_cls.simps by fast
      have wf_cls: "watched_wf_twl_cls M (TWL_Clause W UW)"
        using wf unfolding C by auto
      have wf_lazy: "watched_only_lazy_updates M (TWL_Clause W UW)"
        using wf unfolding C by auto
      have wf_lazy_dec: "watched_wf_twl_cls_decision M (TWL_Clause W UW)"
        using wf unfolding C by auto

      show "watched_wf_twl_cls (tl M) (TWL_Clause W UW)"
        proof -
          consider
              (empty) "W = {#}" and "UW = {#}"
            |  (single) L where "W = {#L#}" and "UW = {#}"
            | (two_watched) L L' where "W = {#L, L'#}"
            using struct_wf size_le_Suc_0_iff[of W] by (auto simp: size_2_iff
              less_eq_2_iff_eq_2_less_eq_Suc_1 subset_eq_mset_single_iff
              distinct_mset_size_2)
          then show ?thesis
            proof cases
              case empty
              then show ?thesis
                by auto
            next
              case (single L)
              then show ?thesis by auto
            next
              case (two_watched L L') note W = this(1)
              have remove_M_M': "remove1_mset K W \<subseteq># image_mset lit_of (mset M)"
                if "remove1_mset K W \<subseteq># image_mset lit_of (mset M')" for K :: "'v literal"
                using subset_mset.order.trans that unfolding M by fastforce
              have K_M'_L: "K \<noteq> lit_of l" if "K \<in> lits_of_l M'" for K :: "'v literal"
                using that n_d unfolding M lits_of_def by (auto simp: image_iff)
              have u_K_M'_L: "K \<noteq> lit_of l" if "-K \<in> lits_of_l M'" for K :: "'v literal"
                using that n_d unfolding M lits_of_def by (metis consistent_interp_def
                  distinct_consistent_interp image_insert insertCI list.simps(15) lits_of_def)
              show ?thesis
                unfolding watched_wf_twl_cls_single_Ball Ball_def
                proof (intro allI impI conjI)
                  fix K K' :: "'v literal"
                  assume
                    KW: "K \<in># W" and
                    KM: "- K \<in> lits_of_l (tl M)" and
                    WM: "remove1_mset K W \<subseteq># image_mset lit_of (mset (tl M))" and
                    K': "K' \<in># W" and
                    KK': "K \<noteq> K'"
                  moreover have "remove1_mset K W \<subseteq># image_mset lit_of (mset M)"
                    using WM subset_mset.order.trans unfolding M by fastforce
                  ultimately have "defined_before M K' (- K)"
                    using wf_cls unfolding M by simp
                  moreover have "K' \<noteq> lit_of l"
                    using K' KK' KW K_M'_L M WM unfolding lits_of_def W by fastforce
                  moreover have "- K \<noteq> lit_of l"
                    using KM K_M'_L M by auto
                  ultimately show "defined_before (tl M) K' (- K)"
                    apply - apply (rule defined_before_tl)
                      using KM KK' unfolding M by (auto simp: defined_before_tl)
                next
                  fix K K' :: "'v literal"
                  assume
                    KW: "K \<in># W" and
                    KM: "- K \<in> lits_of_l (tl M)" and
                    WM: "\<not>remove1_mset K W \<subseteq># image_mset lit_of (mset (tl M))" and
                    K': "K' \<in># UW" and
                    KK': "K' \<notin># W"
                  have LL': "L \<noteq> L'"
                    using struct_wf W by (auto simp: distinct_mset_add)
                  then consider
                      (L') "L = lit_of l" and "K = L'"
                    | (L) "L' = lit_of l" and "K = L"
                    | (rem)  "\<not>remove1_mset K W \<subseteq># image_mset lit_of (mset M)"
                    using KW WM unfolding M W by fastforce
                  then show "- K' \<in> lits_of_l (tl M)"
                    proof cases
                      case rem
                      then have "- K' \<in> lits_of_l (l # M')" and "- K \<in> lits_of_l (l # M')"
                        using wf_cls KW KM K' KK' unfolding watched_wf_twl_cls.simps
                        watched_wf_twl_cls_no_decision.simps M Ball_def
                        by auto
                      moreover
                        have H:
                          "L\<in>#UW \<Longrightarrow> - L \<in> lits_of_l M \<Longrightarrow> L \<notin># W \<Longrightarrow>
                            defined_before M (- L) (- L')"
                          if "L'\<in>#W" "- L' \<in> lits_of_l M" for L' L
                              using that wf_lazy by auto
                        have False if "K' = - lit_of l"
                          proof -
                            have "lit_of l \<notin># W"
                              using KM KW M u_K_M'_L rem two_watched by auto
                            have "-lit_of l \<notin># W"
                              using KK' that by blast
                            moreover
                            then have "defined_before M (-K') (-K)"
                              using H[of K K'] KW KM that K' KK' unfolding M by auto
                            then show False
                              using KK' KW unfolding M defined_before_def that
                              by (auto split: if_splits)
                          qed
                      ultimately show ?thesis
                        using LL' KM  unfolding M by (auto simp: uminus_lit_swap)
                    next
                      case L note L' = this(1) and K = this(2)
                      have [simp]: "lit_of l \<noteq> - L"
                        using K KM K_M'_L M by fastforce
                      have "remove1_mset K W \<subseteq># image_mset lit_of (mset M)"
                        unfolding W K L' M by auto
                      then have "defined_before M L' (-K)"
                        using wf_lazy_dec KW KM unfolding M by (auto simp add: K LL' two_watched)
                      then show ?thesis
                        unfolding L' K M defined_before_def by (auto split: if_splits)
                    next
                      case L' note L = this(1) and K = this(2)
                      have [simp]: "lit_of l \<noteq> - L'"
                        using K KM K_M'_L M by fastforce
                      have "remove1_mset K W \<subseteq># image_mset lit_of (mset M)"
                        unfolding L W K M by auto
                      then have "defined_before M L (-K)"
                        using wf_lazy_dec KW KM unfolding M by (auto simp add: K LL' two_watched)
                      then show ?thesis
                        unfolding K L M defined_before_def by (auto split: if_splits)
                    qed
                qed
            qed
        qed
      show "watched_only_lazy_updates (tl M) (TWL_Clause W UW)"
          unfolding watched_only_lazy_updates.simps Ball_def
        proof (intro allI impI)
          fix K K' :: "'v literal"
          assume "K \<in># W" and
            "K' \<in># UW" and
            K'M: "- K \<in> lits_of_l (tl M)" and
            "- K' \<in> lits_of_l (tl M)" and
            "K' \<notin># W"
          moreover
            have "lit_of l \<noteq> - K'"
              using n_d unfolding M by (metis (no_types) M atm_lit_of_set_lits_of_l
                atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set calculation(4) distinct.simps(2)
                list.sel(3) list.set_map list.simps(9))
          moreover have "watched_only_lazy_updates M C"
            using wf by (auto simp: C)
          moreover have "lit_of l \<notin> lits_of_l M'" using n_d
            by (simp add: M atm_lit_of_set_lits_of_l atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
          ultimately show "defined_before (tl M) (- K') (- K)"
            unfolding defined_before_def
            by (auto simp: M C defined_before_def split: if_split_asm)
        qed
    qed
qed

lemma wf_twl_cls_append:
  assumes
    n_d: "no_dup (M' @ M)" and
    wf: "wf_twl_cls (M' @ M) C"
  shows "wf_twl_cls M C"
  using wf n_d apply (induction M')
    apply simp
  using wf_twl_cls_wf_twl_cls_tl by fastforce


locale well_formed_two_watched_literal_clauses_ops =
  fixes
    wf_watched :: "'cls \<Rightarrow> 'v multiset" and
    wf_unwatched :: "'cls \<Rightarrow> 'v multiset"
begin

definition wf_clause :: "'cls \<Rightarrow> 'v multiset" where
"wf_clause C = wf_watched C + wf_unwatched C"

fun twl_cls_wf :: "'cls \<Rightarrow> 'v multiset twl_clause" where
"twl_cls_wf C = TWL_Clause (wf_watched C) (wf_unwatched C)"

lemma struct_wf_twl_cls_after_switch:
  assumes
    "L \<in># wf_watched C" and
    "L' \<in># wf_unwatched C" and
    twl_cls_wf: "struct_wf_twl_cls (twl_cls_wf C)"
  shows
    "struct_wf_twl_cls
      (TWL_Clause (remove1_mset L (wf_watched C) + {#L'#})
        (remove1_mset L' (wf_unwatched C) + {#L#}))"
proof -
  have LL': "L \<noteq> L'"
    proof
      assume "L = L'"
      then have "count (wf_clause C) L \<ge> 2"
        unfolding wf_clause_def using assms
        by (auto simp: size_2_iff elim!: in_countE)
      moreover have "distinct_mset (wf_clause C)"
        unfolding wf_clause_def using assms twl_cls_wf by auto
      ultimately show False
        by (metis Suc_1 distinct_mset_count_less_1 not_less_eq_eq)
    qed

  have "(remove1_mset L (wf_watched C) + {#L'#}) + (remove1_mset L' (wf_unwatched C) + {#L#}) =
    wf_watched C + wf_unwatched C"
    using assms by (metis insert_DiffM2 union_assoc union_commute)
  moreover have False if L: "L \<in># x1" and L': "L' \<in># x2" and x: "x2 \<subseteq># x1" and
    size: "size x1 \<le> Suc (0::nat)" for x1 x2 :: "'v multiset"
    proof -
      have "x1 = {#L#}"
        using size_le_Suc_0_iff[of x1] size L by auto
      then show False
        using L' x LL' by (auto simp: subset_eq_mset_single_iff)
    qed
  ultimately show ?thesis
    using assms twl_cls_wf
    by (auto simp: size_2_iff size_Diff_singleton elim!: remove1_mset_eqE[of _ L])
qed
end

locale well_formed_two_watched_literal_clauses =
  well_formed_two_watched_literal_clauses_ops wf_watched wf_unwatched
  for
    wf_watched :: "'cls \<Rightarrow> 'v multiset" and
    wf_unwatched :: "'cls \<Rightarrow> 'v multiset" +
  assumes
    twl_cls_wf: "struct_wf_twl_cls (twl_cls_wf C)"
begin



end

experiment
begin
  typedef 'v wf_twl_clause = "{C :: 'v multiset twl_clause. struct_wf_twl_cls C}"
    morphisms twl_clause_of_wf wf_of_twl_clause
  proof
    show "TWL_Clause {#} {#} \<in> ?wf_twl_clause"
      unfolding struct_wf_twl_cls_def by auto
  qed

  setup_lifting type_definition_wf_twl_clause

  lift_definition wf_watched :: "'v wf_twl_clause \<Rightarrow> 'v multiset" is
  "watched :: 'v multiset twl_clause \<Rightarrow> 'v multiset" .

  lift_definition wf_unwatched :: "'v wf_twl_clause \<Rightarrow> 'v multiset" is
  "unwatched :: 'v multiset twl_clause \<Rightarrow> 'v multiset" .

  lift_definition wf_clause :: "'v wf_twl_clause \<Rightarrow> 'v multiset" is
  "clause :: 'v multiset twl_clause \<Rightarrow> 'v multiset" .

  lift_definition map_wf_twl_clause :: "('v multiset \<Rightarrow> 'w multiset) \<Rightarrow> 'v wf_twl_clause \<Rightarrow>
    'w multiset twl_clause" is
  "map_twl_clause ::  ('v multiset \<Rightarrow> 'w multiset) \<Rightarrow> 'v multiset twl_clause \<Rightarrow> 'w multiset twl_clause"
  .

  lemma wf_unwatched_wf_of_twl_clause:
    "struct_wf_twl_cls C \<Longrightarrow> wf_unwatched (wf_of_twl_clause C) = unwatched C"
    by (simp add: wf_of_twl_clause_inverse wf_unwatched.rep_eq)

  lemma wf_watched_wf_of_twl_clause:
    "struct_wf_twl_cls C \<Longrightarrow> wf_watched (wf_of_twl_clause C) = watched C"
    by (simp add: wf_of_twl_clause_inverse wf_watched.rep_eq)

  lemma watched_map_wf_twl_clause:
    "watched (map_wf_twl_clause f C) = f (wf_watched C)"
    by (simp add: map_wf_twl_clause.rep_eq twl_clause.map_sel(1) wf_watched.rep_eq)

  lemma unwatched_map_wf_twl_clause:
    "unwatched (map_wf_twl_clause f C) = f (wf_unwatched C)"
    by (simp add: map_wf_twl_clause.rep_eq twl_clause.map_sel wf_unwatched.rep_eq)

  lemma wf_clause_watched_unwatched: "wf_clause C = wf_watched C + wf_unwatched C"
    by (cases "twl_clause_of_wf C") (auto simp: wf_clause_def wf_watched_def wf_unwatched_def)

  lemma clause_map_wf_twl_clause_wf_clause:
    assumes "\<And>x1 x2. f (x1 + x2) = f x1 + f x2 "
    shows "clause (map_wf_twl_clause f C) = f (wf_clause C)"
    by (cases "twl_clause_of_wf C") (auto simp: assms wf_clause_def map_wf_twl_clause_def)

  interpretation well_formed_two_watched_literal_clauses_ops wf_watched wf_unwatched
    by unfold_locales

  interpretation well_formed_two_watched_literal_clauses wf_watched wf_unwatched
    by unfold_locales (metis mem_Collect_eq twl_clause.collapse twl_clause_of_wf wf_unwatched.rep_eq
      wf_watched.rep_eq twl_cls_wf.simps)

end
end
