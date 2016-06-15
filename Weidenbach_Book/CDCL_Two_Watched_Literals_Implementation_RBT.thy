(*  Title: Implementation of CDCL with Two Watched Literals with Red-Black Trees
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>

    The theory instantiate the locales corresponding to the two watched literals with red-black
    trees to represent a clause and a red-black tree to represent the clauses
*)
theory CDCL_Two_Watched_Literals_Implementation_RBT
imports Main RBT_More CDCL_Abstract_Clause_Representation CDCL_W_Level
  CDCL_Two_Watched_Literals CDCL_Two_Watched_Literals_Implementation
begin

section  \<open>Two-watched-literal implementation with Reed-Black Trees\<close>

text \<open>We instantiate the locales of @{file "CDCL_Two_Watched_Literals_Implementation.thy"}.\<close>


subsection \<open>Definition of a Clause\<close>


subsubsection \<open>Definition and Lifting\<close>

type_synonym lit = nat

interpretation raw_clss where
  get_lit = RBT.lookup and
  mset_cls = RBT_elements_mset and
  get_cls = RBT.lookup and
  mset_clss = RBT_elements_mset
  apply unfold_locales
     apply (metis RBT_elements_def Range.RangeI Range_snd in_multiset_in_set lookup_in_tree set_map)
    apply (metis (no_types, lifting)RBT_elements_def image_iff image_set in_multiset_in_set
      lookup_in_tree prod.exhaust_sel)
   apply (metis RBT_elements_def Range.RangeI Range_snd image_set in_multiset_in_set
     lookup_in_tree)
  apply (metis (no_types, lifting)RBT_elements_def image_iff image_set in_multiset_in_set
    lookup_in_tree prod.exhaust_sel)
  done

definition get_unwatched_lits :: "(nat, 'b) RBT.rbt \<Rightarrow> lit multiset" where
"get_unwatched_lits C = mset (List.filter (op \<le> 2) (RBT.keys C))"

definition get_watched_lits :: "(nat, 'b) RBT.rbt \<Rightarrow> lit multiset" where
"get_watched_lits C =
  (let append_if_not_None =
    (\<lambda>i. case RBT.lookup C i of None \<Rightarrow> op + {#} | Some a \<Rightarrow> op + {#i#}) in
    append_if_not_None 0 (append_if_not_None 1 {#}))"

lemma ge_Suc_Suc_0_iff: "a \<ge> Suc (Suc 0) \<longleftrightarrow> a \<noteq> 0 \<and> a \<noteq> Suc 0"
  by linarith

lemma less_2_iff: "n < 2 \<longleftrightarrow> n = 0 \<or> n = Suc 0"
  by (auto simp: less_2_cases)

lemma filter_mset_or:
  "{# x \<in># M. P x \<or> Q x#} = {# x \<in># M. P x#} + {# x \<in># M. \<not>P x \<and> Q x#}"
  by (auto simp: multiset_eq_iff)

text \<open>Gere is another definition of @{const get_watched_lits}, analog to
  @{const get_unwatched_lits}:\<close>
lemma get_watched_lits_map_le_2:
  "get_watched_lits C = mset (List.filter (\<lambda>L. \<not>L \<ge> 2) (RBT.keys C))"
proof -
  have [iff]: "\<not>a \<ge> (2::nat) \<longleftrightarrow> a < 2" for a :: nat
    by auto
  have [iff]: "0 < x \<and> x = Suc 0 \<longleftrightarrow> x = Suc 0" for x :: nat
    by auto
  show ?thesis
    by (auto simp: get_watched_lits_def mset_filter less_2_iff filter_mset_or
      filter_eq_replicate_mset count_RBT_keys)
qed

definition get_watched_lits_list :: "(nat, 'b) RBT.rbt \<Rightarrow> lit list" where
"get_watched_lits_list C =
  (let append_if_not_None =
    (\<lambda>i. case RBT.lookup C i of None \<Rightarrow> id | Some a \<Rightarrow> op # i) in
    append_if_not_None 0 (append_if_not_None 1 []))"

lemma get_watched_lits_mset_get_watched_lits_list:
  "get_watched_lits C = mset (get_watched_lits_list C)"
  by (auto simp: get_watched_lits_def get_watched_lits_list_def ac_simps
    split: option.splits)

definition lits_twl_clause_of_RBT :: "(nat, 'a) RBT.rbt \<Rightarrow> nat multiset twl_clause"  where
"lits_twl_clause_of_RBT C = TWL_Clause (get_watched_lits C) (get_unwatched_lits C)"

fun RBT_clause :: "(nat, 'v) RBT.rbt \<Rightarrow> 'v multiset" where
"RBT_clause C = mset (RBT_elements C)"

text \<open>We expect the following link between @{const RBT_clause}, @{const get_watched_lits} and
  @{const get_unwatched_lits}:\<close>
lemma RBT_clause_get_watched_lits_get_unwatched_lits:
  "RBT_clause C = image_mset (the o RBT.lookup C) (get_watched_lits C + get_unwatched_lits C)"
  unfolding get_watched_lits_map_le_2 get_unwatched_lits_def
  by (auto simp: ac_simps RBT_elements_mset_image_mset_lookup_keys_mset)


text \<open>The following function is a bit more general than needed: we only call it when @{term i}
  and @{term j} are well-formed indexes. However, this more general version allows to lift the
  definition unconditionally.\<close>
fun swap_lit_safe :: "('a::linorder, 'b) RBT.rbt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b) RBT.rbt" where
"swap_lit_safe C i j =
  (case (RBT.lookup C i, RBT.lookup C j) of
    (Some i', Some j') \<Rightarrow> RBT.insert j i' (RBT.insert i j' C)
  | _ \<Rightarrow> C)"


typedef 'v wf_clause_RBT =
  "{C :: (nat, 'v) RBT.rbt. struct_wf_twl_cls (lits_twl_clause_of_RBT C)}"
  morphisms conc_RBT_cls abs_RBT_cls
proof
  show "RBT.empty \<in> ?wf_clause_RBT"
    by (auto simp: get_watched_lits_def get_unwatched_lits_def lits_twl_clause_of_RBT_def)
qed

setup_lifting type_definition_wf_clause_RBT
lift_definition wf_watched_lits :: "'v wf_clause_RBT \<Rightarrow> lit multiset" is get_watched_lits .
lift_definition wf_watched_lits_list :: "'v wf_clause_RBT \<Rightarrow> lit list" is get_watched_lits_list .
lift_definition wf_unwatched_lits :: "'v wf_clause_RBT \<Rightarrow> lit multiset" is get_unwatched_lits .
lift_definition lit_lookup :: "'v wf_clause_RBT \<Rightarrow> lit \<rightharpoonup> 'v" is RBT.lookup .
lift_definition lit_keys :: "'v wf_clause_RBT \<Rightarrow> lit multiset" is "\<lambda>C. mset (RBT.keys C)" .
lift_definition lit_entries :: "'v wf_clause_RBT \<Rightarrow> (nat \<times> 'v) list" is RBT.entries .
lift_definition wf_RBT_clause :: "'v wf_clause_RBT \<Rightarrow> 'v multiset" is RBT_clause .

lemma wf_RBT_clause_wf_watched_lits_wf_unwatched_lits:
  "wf_RBT_clause C = image_mset (the o lit_lookup C) (wf_watched_lits C + wf_unwatched_lits C)"
  by (metis RBT_clause_get_watched_lits_get_unwatched_lits lit_lookup.rep_eq wf_RBT_clause.rep_eq
    wf_unwatched_lits.rep_eq wf_watched_lits.rep_eq)

lemma lit_keys_wf_watched_lits_wf_unwatched_lits:
  "lit_keys C = wf_watched_lits C + wf_unwatched_lits C"
  unfolding lit_keys.rep_eq wf_unwatched_lits.rep_eq wf_watched_lits.rep_eq
  get_unwatched_lits_def get_watched_lits_map_le_2
  by (auto simp: ac_simps simp del: image_mset_union)

lemma wf_watched_lits_mset_wf_watched_lits_list:
  "wf_watched_lits C = mset (wf_watched_lits_list C)"
  by (auto simp: get_watched_lits_mset_get_watched_lits_list wf_watched_lits.rep_eq
    wf_watched_lits_list.rep_eq)


subsubsection \<open>Instantiations\<close>

interpretation well_formed_two_watched_literal_clauses_ops where
  wf_watched = wf_watched_lits and
  wf_unwatched = wf_unwatched_lits
  by unfold_locales

interpretation raw_RBT_clause: well_formed_two_watched_literal_clauses_ops where
  wf_watched = get_watched_lits and
  wf_unwatched = get_unwatched_lits
  by unfold_locales

interpretation well_formed_two_watched_literal_clauses where
  wf_watched = wf_watched_lits and
  wf_unwatched = wf_unwatched_lits
proof (unfold_locales)
  fix C :: "'a wf_clause_RBT"
  have "struct_wf_twl_cls (TWL_Clause (get_watched_lits (conc_RBT_cls C))
    (get_unwatched_lits (conc_RBT_cls C)))"
    using conc_RBT_cls unfolding lits_twl_clause_of_RBT_def by blast
  then show "struct_wf_twl_cls (twl_cls_wf C)"
    by (simp add: wf_unwatched_lits.rep_eq wf_watched_lits.rep_eq)
qed

lemma lits_twl_clause_of_RBT_swap_lit_safe_commute_index:
  "lits_twl_clause_of_RBT (swap_lit_safe C i j) = lits_twl_clause_of_RBT (swap_lit_safe C j i)"
proof -
  have "get_watched_lits (RBT.insert j x2 (RBT.insert i x2a C)) =
      get_watched_lits (RBT.insert i x2a (RBT.insert j x2 C))"
    if "RBT.lookup C i = Some x2" and "RBT.lookup C j = Some x2a" for x2 x2a
    by (metis (no_types, lifting) that RBT.map_of_entries get_watched_lits_def lookup_insert
     rbt_insert_swap(1))
  moreover have "get_unwatched_lits (RBT.insert j x2 (RBT.insert i x2a C)) =
    get_unwatched_lits (RBT.insert i x2a (RBT.insert j x2 C))"
    if "RBT.lookup C i = Some x2" and "RBT.lookup C j = Some x2a" for x2 x2a
    by (metis get_unwatched_lits_def keys_def_alt option.sel rbt_insert_swap(1) that)
  ultimately show ?thesis
    by (auto simp: lits_twl_clause_of_RBT_def split: option.splits)
qed

lemma lits_twl_clause_of_RBT_swap_lit_safe:
  assumes "i \<le> j" and "struct_wf_twl_cls (TWL_Clause (get_watched_lits C) (get_unwatched_lits C))"
  shows "lits_twl_clause_of_RBT (swap_lit_safe C i j) = lits_twl_clause_of_RBT C"
proof -
  consider
      (not_empty) i' j' where "RBT.lookup C i = Some i'" and "RBT.lookup C j = Some j'"
    | (empty) "RBT.lookup C i = None \<or> RBT.lookup C j = None"
    by (cases "RBT.lookup C i"; cases "RBT.lookup C j") auto
  then show ?thesis
    proof cases
      case empty
      then show ?thesis by (auto simp: lits_twl_clause_of_RBT_def split: option.splits)
    next
      case (not_empty i' j') note i' = this(1) and j' = this(2)

      consider
          (both_watched) "i < 2" and "j < 2"
        | (i_watched) "i < 2" and "j \<ge> 2"
        | (both_unwatched) "i \<ge> 2" and "j \<ge> 2"
        using \<open>i \<le> j\<close> by linarith
      then show ?thesis
        proof cases
          case both_watched
          moreover have "{#j', i'#} = {#i', j'#}" by (auto simp: multiset_eq_iff)
          ultimately show ?thesis
            using i' j'
            by (auto simp: lits_twl_clause_of_RBT_def get_watched_lits_def get_unwatched_lits_def
               mset_filter mset_RBT_keys_insert
              split: option.splits
              dest!: less_2_cases)
        next
          case i_watched
          moreover have "{#x, j'#} = {#j', x#}" for x by (auto simp: multiset_eq_iff)
          moreover have "j \<in> fst ` {a \<in> set (RBT.entries C). 2 \<le> fst a} \<longleftrightarrow>
            RBT.lookup C j \<noteq> None \<and> j \<ge> 2"
            by (auto simp: lookup_in_tree keys_entries image_iff)
          ultimately show ?thesis
            using i' j' unfolding mset_filter mset_map
            by (auto simp: lits_twl_clause_of_RBT_def get_watched_lits_def get_unwatched_lits_def
              mset_filter mset_RBT_keys_insert in_RBT_keys_lookup
              split: option.splits
              dest: less_2_cases)
        next
          case (both_unwatched)
          have "(i, i') \<in> set (RBT.entries C)"
            using i' by (simp add: lookup_in_tree)
          then have "i \<in> fst ` {p \<in> set (RBT.entries C). 2 \<le> fst p}"
            by (auto simp add: single_remove1_mset_eq lookup_in_tree keys_entries image_iff
              \<open>2 \<le> i\<close>)
          then have i: "{#i#} + remove1_mset i (mset (map fst [L\<leftarrow>RBT.entries C. 2 \<le> fst L])) =
            mset (map fst [L\<leftarrow>RBT.entries C . 2 \<le> fst L])"
            using i'
            by (auto simp add: single_remove1_mset_eq)
           have [iff]: "i \<in> fst ` {a \<in> set (RBT.entries C). 2 \<le> fst a} \<longleftrightarrow>
            RBT.lookup C i \<noteq> None \<and> i \<ge> 2" for i :: nat
            by (auto simp: lookup_in_tree keys_entries image_iff)
          show ?thesis
            using i' j' both_unwatched
            by (auto simp: lits_twl_clause_of_RBT_def get_watched_lits_def get_unwatched_lits_def
              mset_filter mset_RBT_keys_insert in_RBT_keys_lookup)
        qed
    qed
qed

lift_definition swap_lit :: "'v wf_clause_RBT \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v wf_clause_RBT" is
  swap_lit_safe
proof -
  fix C :: "(nat, 'v) RBT.rbt" and i j :: nat
  assume wf: "struct_wf_twl_cls (lits_twl_clause_of_RBT C)"
  let ?D = "swap_lit_safe C i j"
  {
    fix i j :: nat
    let ?D = "swap_lit_safe C i j"
    assume ij: "i \<le> j"
    have H: "x2a \<in> snd ` {x \<in> set (RBT.entries C). 2 \<le> fst x}"
      if "\<not> j < 2" and "RBT.lookup C j = Some x2a" for x2a :: 'v
      using that by (metis (no_types, lifting) Range.RangeI Range_snd leI lookup_in_tree
        mem_Collect_eq prod.sel(1))
    have "struct_wf_twl_cls (TWL_Clause (get_watched_lits ?D) (get_unwatched_lits ?D))"
      apply (subst lits_twl_clause_of_RBT_swap_lit_safe[unfolded lits_twl_clause_of_RBT_def])
      using wf ij by (auto simp del: struct_wf_twl_cls.simps
        simp: lits_twl_clause_of_RBT_def split: option.splits)
  } note H = this(1)

  consider
      (ij) "i \<le> j"
    | (ji) "j \<le> i"
    by linarith
  then show "struct_wf_twl_cls (lits_twl_clause_of_RBT ?D)"
    proof cases
      case ij
      then show ?thesis using H unfolding lits_twl_clause_of_RBT_def by blast
    next
      case ji
      show ?thesis
        unfolding lits_twl_clause_of_RBT_def[symmetric]
        apply (subst lits_twl_clause_of_RBT_swap_lit_safe_commute_index[of C i j])
        using ji H[of j i] unfolding lits_twl_clause_of_RBT_def[symmetric] by blast
    qed
qed

fun it_of_watched_ordered :: "'a wf_clause_RBT \<Rightarrow> 'a \<Rightarrow> lit list"  where
"it_of_watched_ordered C L =
  (case wf_watched_lits_list C of
    [i] \<Rightarrow> [i]
  | [i, j] \<Rightarrow>
    if lit_lookup C i = Some L
    then [i, j]
    else [j, i])"

fun list_to_RBT :: "'a list \<Rightarrow> nat \<Rightarrow> (nat, 'a) RBT.rbt"  where
"list_to_RBT [] _ = RBT.empty" |
"list_to_RBT (L # C) n = RBT.insert n L (list_to_RBT C (Suc n))"

text \<open>The following functions works only if there are no duplicate in @{term C}. Otherwise, the
  result is not specified.\<close>
fun cls_of_twl_list :: "'a list \<Rightarrow> 'a wf_clause_RBT" where
"cls_of_twl_list C = abs_RBT_cls (list_to_RBT C 0)"

lemma RBT_lookup_list_to_RBT:
  "RBT.lookup (list_to_RBT C i) j = (if j \<ge> i \<and> j < i + length C then Some (C ! (j - i)) else None)"
  by (induction C i rule: list_to_RBT.induct) auto

lemma mset_RBT_entries_list_to_RBT:
  "mset (RBT.entries (list_to_RBT C i)) = mset (zip [i..< i+length C] C)"
proof (induction C arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons L C) note IH = this(1)[of]
  consider
    (empty) "[i..<i + length C] = []" |
    (first) "[i..<i + length C] = i # [Suc i..<i + length C]"
    by (meson upt_rec)
  then show ?case
    proof cases
      case empty
      then show ?thesis
        by (auto simp: mset_RBT_entries_insert ac_simps)
    next
      case first
      then have "[i..<Suc (i + length C)] = i # [Suc i..<Suc (i + length C)]"
        by (simp add: upt_rec)
      then show ?thesis
        by (auto simp: mset_RBT_entries_insert ac_simps IH RBT_lookup_list_to_RBT
          remove_1_mset_id_iff_notin
          dest: List.set_zip_leftD)
    qed
qed

lemma mset_zip_image_mset:
  "mset (zip xs ys) = {# (xs!i, ys!i). i \<in># mset [0..< min (length xs) (length ys)] #}"
proof (induction xs ys rule: list_induct2')
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case 3
  then show ?case by simp
next
  case (4 x xs y ys)
  have "[0..<min (length (x # xs)) (length (y # ys))] =
    0 # map Suc [0..<min (length xs) (length ys)]"
    by (subst upt_rec) (simp add: map_Suc_upt)
  then show ?case
    using 4 by (auto simp: mset_map)
qed

lemma mset_set_eq:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> mset_set A = mset_set B \<longleftrightarrow> A = B"
  using finite_set_mset_mset_set by fastforce+

lemma filter_image_mset:
  "{# L \<in># {#P x. x \<in># M#}. Q L#} = {#P x| x \<in># M. Q (P x)#}"
  by (induction M) auto

lemma image_mset_nth_upt:
  "image_mset (op ! C) (mset_set {0..<length C}) = mset C"
proof -
  have C: "mset_set {0..<length C} = mset [0 ..< length C]"
    by auto
  show ?thesis
    unfolding C image_mset_mset_mset_map by (auto simp: map_nth)
qed

lemma image_mset_snd_mset_RBT_entries:
  "image_mset snd (mset (RBT.entries (list_to_RBT C 0))) = mset C"
  by (auto simp: mset_zip_image_mset filter_image_mset image_mset_union[symmetric]
      image_mset_nth_upt mset_RBT_entries_list_to_RBT)

lemma wf_RBT_clause_cls_of_twl_list:
  assumes dist_C: "distinct C"
  shows "wf_RBT_clause (cls_of_twl_list C) = mset C"
proof -
  have C_size_1: "\<exists>L. C = [L]" if "\<not> Suc 0 < length C" and "C \<noteq> []"
    using that by (cases C) auto
  have [iff]:  "x < length C \<and> 2 \<le> [0..<length C] ! x \<longleftrightarrow> x \<ge> 2 \<and> x < length C" for x :: nat
    by auto
  have "{x::nat. x < 2} = {0, 1}"
    by auto
  then have C: "{#C ! 0, C ! Suc 0#} = image_mset (op ! C) (mset_set {x. x < 2})"
    by auto
  have mset_set_2: "mset_set {x. x < 2} + mset_set {x. 2 \<le> x \<and> x < length C} =
    mset [0 ..< length C]" if "length C \<ge> 2"
    using that by (subst mset_set_Union[symmetric]) (auto simp: mset_set_eq)
  have "distinct_mset (filter_mset (op \<le> 2) (RBT_keys_mset (list_to_RBT C 0)))"
    by (metis RBT.distinct_keys distinct_mset_add distinct_mset_distinct multiset_partition)
  then have [simp]: "struct_wf_twl_cls (lits_twl_clause_of_RBT (list_to_RBT C 0))"
    by (auto simp: lits_twl_clause_of_RBT_def get_watched_lits_def get_unwatched_lits_def
        RBT_lookup_list_to_RBT  distinct_mset_add_single ac_simps
         mset_RBT_keys_insert mset_filter
      dest!: C_size_1)
  show ?thesis
    unfolding cls_of_twl_list.simps wf_RBT_clause.rep_eq
    by (auto simp: abs_RBT_cls_inverse mset_map  image_mset_snd_mset_RBT_entries
      RBT_elements_def)
qed

fun twl_lits_twl_clause_of_RBT where
"twl_lits_twl_clause_of_RBT C =
  (let append_if_not_None =
    (\<lambda>i. case RBT.lookup C i of None \<Rightarrow> id | Some a \<Rightarrow> Cons a) in
  TWL_Clause (get_watched_lits C) (get_unwatched_lits C))"

lemma RBT_lookup_swap_lit_safe:
  assumes "i \<in> set (RBT.keys C)" and "j \<in> set (RBT.keys C)"
  shows "RBT.lookup (swap_lit_safe C j i) =
     RBT.lookup C(j \<mapsto> the (RBT.lookup C i), i \<mapsto> the (RBT.lookup C j))"
  using assms by (auto simp: keys_entries lookup_in_tree[symmetric])

interpretation abstract_clause_representation_ops where
  wf_watched_lits = "wf_watched_lits :: 'v literal wf_clause_RBT \<Rightarrow> lit multiset" and
  wf_unwatched_lits = wf_unwatched_lits and
  lit_lookup = lit_lookup and
  lit_keys = lit_keys and
  swap_lit = swap_lit and
  it_of_watched_ordered = it_of_watched_ordered and
  cls_of_twl_list = cls_of_twl_list
  by unfold_locales

lemma size_filter_mset_RBT_entries_fst_eq:
  assumes P: "\<And>x. P x \<Longrightarrow> fst x = a"
  shows
    "size {# x \<in># mset (RBT.entries C). P x#} =
      (if RBT.lookup C a \<noteq> None \<and> P (a, the (RBT.lookup C a)) then 1 else 0)"
proof -
  have [dest]: "RBT.lookup C aa = Some b \<Longrightarrow> P (aa, b) \<Longrightarrow> P (a, the (RBT.lookup C a))" for aa b
    using assms by auto
  have "{# x \<in># mset (RBT.entries C). P x#} =
    (if RBT.lookup C a \<noteq> None \<and> P (a, the (RBT.lookup C a))
    then {#(a, the (RBT.lookup C a))#}
    else {#})"
    by (rule distinct_set_mset_eq)
    (auto simp: distinct_mset_filter distinct_rbt_entries lookup_in_tree[symmetric]
      dest: P)
  then show ?thesis by auto
qed

lemma image_mset_fst_mset_RBT_entries:
  "{#f (fst x). x \<in># {# x \<in># mset (RBT.entries C). P (fst x)#}#} =
    {#f k. k \<in># {# k \<in># mset (RBT.keys C). P k#}#}" (is "?A = ?B")
proof -
  let ?M = "{# x \<in># mset (RBT.entries C). P (fst x)#}"
  have "?A = image_mset f (image_mset fst ?M)"
    by auto
  also have "image_mset fst ?M = {# fst x|x \<in># mset (RBT.entries C). P (fst x)#}"
    by auto
  moreover have "{# fst x|x \<in># mset (RBT.entries C). P (fst x)#} = {# k \<in># mset (RBT.keys C). P k#}"
    by (auto simp: image_mset_filter_swap image_mset_fst_RBT_entries_keys)
  ultimately show ?thesis by fastforce
qed

lemma fst_filter_entries:
  "fst ` {a \<in> set (RBT.entries C). P (fst a)} = {a \<in> set (RBT.keys C). P a}"
  by (auto simp: lookup_in_tree keys_entries image_iff)

lemma single_remove1_mset_single_remove1_mset_eq:
  "{#j#} + remove1_mset j ({#i#} + remove1_mset i M) = M \<longleftrightarrow> i \<in>#M \<and> j \<in># M"
  by (auto simp: multiset_eq_iff ac_simps not_in_iff
    count_greater_zero_iff[symmetric]
    simp del: count_greater_zero_iff)


lemma
  assumes
    "RBT.lookup C i = Some i'" and
    "RBT.lookup C j = Some j'"
  shows
    get_watched_lits_swap_lit_safe:
       "get_watched_lits (swap_lit_safe C i j) = get_watched_lits C" and
    get_unwatched_lits_swap_lit_safe:
      "get_unwatched_lits (swap_lit_safe C i j) = get_unwatched_lits C"
  using assms
  by (auto simp: get_watched_lits_map_le_2 get_unwatched_lits_def
    mset_filter  keys_entries lookup_in_tree[symmetric] mset_RBT_keys_insert)


lemma
  assumes
    "lit_lookup C i = Some i'" and
    "lit_lookup C j = Some j'"
  shows
    wf_watched_lits_swap_lit:
      "wf_watched_lits (swap_lit C i j) = wf_watched_lits C" and
    wf_unwatched_lits_swap_lit:
      "wf_unwatched_lits (swap_lit C i j) = wf_unwatched_lits C"
  using assms
  by (auto simp: wf_watched_lits.rep_eq get_watched_lits_swap_lit_safe lit_lookup.rep_eq
    swap_lit.rep_eq get_unwatched_lits_swap_lit_safe wf_unwatched_lits.rep_eq
    simp del: swap_lit_safe.simps)

lemma count_get_unwatched_lits_if:
  "count (get_unwatched_lits C) j = (if j \<ge> 2 \<and> RBT.lookup C j \<noteq> None then 1 else 0)"
  using image_mset_fst_mset_RBT_entries[of id _ C] RBT.distinct_keys[of C]
  by (auto simp: get_unwatched_lits_def mset_map mset_filter lookup_in_tree keys_entries
    not_in_iff[symmetric] image_mset_fst_RBT_entries_keys
      distinct_count_atmost_1)

lemma count_wf_unwatched_lits_if:
  "count (wf_unwatched_lits C) j = (if j \<ge> 2 \<and> lit_lookup C j \<noteq> None then 1 else 0)"
  by (auto simp: wf_unwatched_lits.rep_eq lit_lookup.rep_eq count_get_unwatched_lits_if)

lemma count_get_watched_lits_if:
  "count (get_watched_lits C) j = (if \<not>j \<ge> 2 \<and> RBT.lookup C j \<noteq> None then 1 else 0)"
  using image_mset_fst_mset_RBT_entries[of id "\<lambda>a. \<not> 2 \<le> a" C] RBT.distinct_keys[of C]
  by (auto simp: get_watched_lits_map_le_2 mset_map mset_filter lookup_in_tree keys_entries
    not_in_iff[symmetric] image_mset_fst_RBT_entries_keys
      distinct_count_atmost_1)

lemma count_wf_watched_lits_if:
  "count (wf_watched_lits C) j = (if \<not>j \<ge> 2 \<and> lit_lookup C j \<noteq> None then 1 else 0)"
  by (auto simp: wf_watched_lits.rep_eq lit_lookup.rep_eq count_get_watched_lits_if)

lemma add_single_add_single_remove1_mset_remove1_mset_id:
  "{#i'#} + ({#j'#} + remove1_mset i' (remove1_mset j' M)) = M \<longleftrightarrow>
    (i' = j' \<and> count M i' \<ge> 2) \<or> (i' \<noteq> j' \<and> i' \<in># M \<and> j' \<in># M)"
  by (auto simp: multiset_eq_iff ac_simps count_greater_zero_iff[symmetric]
    simp del: count_greater_zero_iff)

lemma size_filter_eq_replicate_count:
   "size {#x \<in># M. x = j'#} = count M j'"
   by (simp add: filter_eq_replicate_mset)

lemma twl_clause_swap_lit_safe:
  assumes "i \<le> j"
  shows "twl_clause (swap_lit C i j) =
  (case (lit_lookup C i, lit_lookup C j) of
    (Some i', Some j') \<Rightarrow>
      if i < 2 \<and> j < 2
      then twl_clause C
      else if i < 2 \<and> j \<ge> 2
        then TWL_Clause ({#j'#} + remove1_mset i' (wf_watched C))
          ({#i'#} + remove1_mset j' (wf_unwatched C))
        else twl_clause C
  | _ \<Rightarrow> twl_clause C)"
proof -
  consider
      (not_empty) i' j' :: "'a literal" where "lit_lookup C i = Some i'" and
        "lit_lookup C j = Some j'"
    | (empty) "lit_lookup C i = None \<or> lit_lookup C j = None"
    by (cases "lit_lookup C i"; cases "lit_lookup C j") auto
  then show ?thesis
    proof cases
      case empty
      then show ?thesis by (auto simp: lits_twl_clause_of_RBT_def swap_lit.rep_eq
        lit_lookup.rep_eq wf_watched_lits.rep_eq wf_unwatched_lits.rep_eq
         split: option.splits)
    next
      case (not_empty i' j') note i' = this(1) and j' = this(2)

      consider
          (both_watched) "i < 2" and "j < 2"
        | (i_watched) "i < 2" and "j \<ge> 2"
        | (both_unwatched) "i \<ge> 2" and "j \<ge> 2"
        using \<open>i \<le> j\<close> by linarith
      then show ?thesis
        proof cases
          case both_watched
          have i:
            "{#the (if x = a then Some i' else (RBT.lookup (conc_RBT_cls C)(b \<mapsto> k')) x).
               x \<in># filter_mset (op \<le> 2) (RBT_keys_mset (conc_RBT_cls C))#} =
            {#the (RBT.lookup (conc_RBT_cls C) x).
               x \<in># filter_mset (op \<le> 2) (RBT_keys_mset (conc_RBT_cls C))#}"
              if "a < 2" and "b < 2" for a b :: nat and i' j' k' :: "'a literal"
            using that apply -
            by (rule image_mset_cong2; auto simp: )
          have "{#j', i'#} = {#i', j'#}" by (auto simp: multiset_eq_iff)
          then show ?thesis
            using i' j' both_watched
            by (auto simp:  get_watched_lits_def get_unwatched_lits_def
                swap_lit.rep_eq lit_lookup.rep_eq wf_watched_lits.rep_eq wf_unwatched_lits.rep_eq i
                mset_RBT_keys_insert mset_filter
              split: option.splits
              dest!: less_2_cases)
        next
          case i_watched
          moreover
            then have "{#the (if x = j then Some i' else (RBT.lookup (conc_RBT_cls C)(i \<mapsto> j')) x).
              x \<in># wf_watched_lits C#} = {#j'#} + remove1_mset i' (wf_watched C)"
              using i' j' unfolding mset_filter mset_map
              apply (auto simp add: if_distrib filter_eq_replicate_mset lit_lookup.rep_eq
                wf_watched_def count_wf_watched_lits_if filter_mset_neq
                image_mset_If image_mset_remove1_mset_if not_in_iff)
              done
          moreover
            have "{#the (if x = j then Some i' else (RBT.lookup (conc_RBT_cls C)(i \<mapsto> j')) x).
              x \<in># wf_unwatched_lits C#} = {#i'#} + remove1_mset j' (wf_unwatched C)"
              using i' j' i_watched unfolding mset_filter mset_map
              by (auto simp add: if_distrib filter_eq_replicate_mset lit_lookup.rep_eq
                wf_unwatched_def count_wf_unwatched_lits_if filter_mset_neq
                image_mset_If image_mset_remove1_mset_if not_in_iff)
          ultimately show ?thesis
            using i' j' unfolding mset_filter mset_map
            by (auto simp: lit_lookup.rep_eq swap_lit.rep_eq
              wf_watched_lits_swap_lit wf_unwatched_lits_swap_lit
              RBT_lookup_swap_lit_safe keys_entries image_iff lookup_in_tree[symmetric]
              split: option.splits simp del: swap_lit_safe.simps)
        next
          case (both_unwatched)
          have i_unwatched: "i \<in># wf_unwatched_lits C"
            using i' both_unwatched
            by (auto simp: count_greater_zero_iff[symmetric] count_wf_unwatched_lits_if
              simp del: count_greater_zero_iff)
          then have lookup_i_in_lookup_unwatched: "the (RBT.lookup (conc_RBT_cls C) i)
             \<in> (\<lambda>x. the (RBT.lookup (conc_RBT_cls C) x)) ` set_mset (wf_unwatched_lits C)"
             by simp
          then have i'_lookup_unwatched[simp]: "i' \<in> (\<lambda>x. the (RBT.lookup (conc_RBT_cls C) x)) `
            set_mset (wf_unwatched_lits C)"
            using i' by (auto simp: lit_lookup.rep_eq)

          have j_unwatched: "j \<in># wf_unwatched_lits C"
            using j' both_unwatched
            by (auto simp: count_greater_zero_iff[symmetric] count_wf_unwatched_lits_if
              simp del: count_greater_zero_iff)
          then have lookup_j_in_lookup_unwatched: "the (RBT.lookup (conc_RBT_cls C) j)
             \<in> (\<lambda>x. the (RBT.lookup (conc_RBT_cls C) x)) ` set_mset (wf_unwatched_lits C)"
             by simp
          then have j'_lookup_unwatched[simp]: "j' \<in> (\<lambda>x. the (RBT.lookup (conc_RBT_cls C) x)) `
            set_mset (wf_unwatched_lits C)"
            using j' by (auto simp: lit_lookup.rep_eq)

          have "{#the (if x = j then Some i' else (RBT.lookup (conc_RBT_cls C)(i \<mapsto> j')) x).
              x \<in># wf_watched_lits C#} =
            {#the (RBT.lookup (conc_RBT_cls C) L). L \<in># wf_watched_lits C#}"
          using i' j' both_unwatched
          by (auto simp: if_distrib filter_eq_replicate_mset lit_lookup.rep_eq
              wf_unwatched_def filter_mset_neq
              image_mset_If image_mset_remove1_mset_if not_in_iff
              count_wf_watched_lits_if
            split: option.splits simp del: swap_lit_safe.simps)
          moreover
            have "2 \<le> count {#the (RBT.lookup (conc_RBT_cls C) x). x \<in># wf_unwatched_lits C#} j'"
              if ij: "j \<noteq> i"  and  "i' = j'"
              proof -
                let ?M = "{#the (RBT.lookup (conc_RBT_cls C) x). x \<in># wf_unwatched_lits C#}"
                have "{#i, j#} \<subseteq># wf_unwatched_lits C"
                  using i_unwatched j_unwatched ij by (auto simp add: subseteq_mset_def)
                then have "image_mset (\<lambda>i. the (lit_lookup C i)) {#i, j#} \<subseteq># ?M"
                  using image_mset_subseteq_mono unfolding lit_lookup.rep_eq by blast
                then have "{#i', j'#} \<subseteq># ?M"
                  using i' j' by auto
                then have "count {#i', j'#} j' \<le> count ?M j'"
                  by (meson mset_less_eq_count)
                then show ?thesis
                  by (auto simp: \<open>i' = j'\<close>)
              qed
            then have "{#the (if x = j then Some i' else (RBT.lookup (conc_RBT_cls C)(i \<mapsto> j')) x).
                 x \<in># wf_unwatched_lits C#} =
               {#the (RBT.lookup (conc_RBT_cls C) L). L \<in># wf_unwatched_lits C#}"
              using i' j' both_unwatched
              by (auto simp: if_distrib filter_eq_replicate_mset lit_lookup.rep_eq
                  wf_unwatched_def filter_mset_neq
                  image_mset_If image_mset_remove1_mset_if not_in_iff
                  count_wf_unwatched_lits_if single_remove1_mset_eq
                  lookup_in_tree[symmetric]
                  count_greater_zero_iff[symmetric] ac_simps
                  add_single_add_single_remove1_mset_remove1_mset_id
                  simp del: count_greater_zero_iff
                split: option.splits if_splits simp del: swap_lit_safe.simps)
          ultimately show ?thesis
            using i' j' both_unwatched
            by (auto simp: lit_lookup.rep_eq swap_lit.rep_eq
              wf_watched_lits_swap_lit wf_unwatched_lits_swap_lit
              RBT_lookup_swap_lit_safe keys_entries image_iff lookup_in_tree[symmetric]
              split: option.splits simp del: swap_lit_safe.simps)
        qed
    qed
qed

lemma twl_clause_swap_lit:
  assumes
    i: "i \<in># wf_watched_lits C" and
    j: "j \<in># wf_unwatched_lits C"
  shows
    "twl_clause (swap_lit C i j) =
       TWL_Clause
        ({#the (lit_lookup C j)#} + remove1_mset (the (lit_lookup C i)) (wf_watched C))
        ({#the (lit_lookup C i)#} + remove1_mset (the (lit_lookup C j)) (wf_unwatched C))"
proof -
  have
    i': "lit_lookup C i \<noteq> None" and
    j': "lit_lookup C j \<noteq> None"
    using i j by (auto simp: wf_unwatched_lits_def get_unwatched_lits_def
      wf_watched_lits_def get_watched_lits_map_le_2
      in_RBT_keys_lookup
      lookup_in_tree[symmetric] lit_lookup.rep_eq)
  have i: "i < 2"
    using i by (metis count_greater_zero_iff count_wf_watched_lits_if leI less_numeral_extra(3))
  moreover have j: "j \<ge> 2"
    using j by (auto simp: wf_unwatched_lits_def get_unwatched_lits_def)
  ultimately have "i \<le> j"
      by auto
  show ?thesis
    using i j i' j' unfolding twl_clause_swap_lit_safe[OF \<open>i \<le> j\<close>]
    by (auto split: option.splits)
qed

interpretation RBT: abstract_clause_representation where
  wf_watched_lits = "wf_watched_lits :: 'v literal wf_clause_RBT \<Rightarrow> lit multiset" and
  wf_unwatched_lits = wf_unwatched_lits and
  lit_lookup = lit_lookup and
  lit_keys = lit_keys and
  swap_lit = swap_lit and
  it_of_watched_ordered = it_of_watched_ordered and
  cls_of_twl_list = "cls_of_twl_list :: 'v literal list \<Rightarrow> 'v literal wf_clause_RBT"
proof unfold_locales
  show "distinct_mset (lit_keys C)" for C :: "'a wf_clause_RBT"
    by (simp add: lit_keys.rep_eq)

  show "i \<in># lit_keys C \<longleftrightarrow> lit_lookup C i \<noteq> None" for i :: nat and C :: "'a wf_clause_RBT"
    by (auto simp add: lit_keys.rep_eq lookup_in_tree lit_lookup.rep_eq keys_entries)

  show "lit_keys C = wf_clause C" for C :: "'a wf_clause_RBT"
    by (auto simp: lit_keys_wf_watched_lits_wf_unwatched_lits wf_clause_def)

  show "mset (it_of_watched_ordered C L) = wf_watched_lits C \<and>
    lit_lookup C (hd (it_of_watched_ordered C L)) = Some L"
    if "L \<in># watched (twl_clause C)" for C:: "'a literal wf_clause_RBT" and L :: "'a literal"
    using that by (auto simp: wf_watched_lits_mset_wf_watched_lits_list
      wf_watched_lits_list.rep_eq get_watched_lits_list_def lit_lookup.rep_eq ac_simps
      split: list.splits option.splits)

  show "clause_of_cls (cls_of_twl_list D) = mset D"
    if "distinct D" for D :: "'a literal list"
    proof -
      have "wf_RBT_clause (cls_of_twl_list D) = clause (twl_clause (cls_of_twl_list D))"
        by (simp add: wf_RBT_clause_wf_watched_lits_wf_unwatched_lits)
      then show ?thesis
        by (metis (no_types) clause_of_cls_def that wf_RBT_clause_cls_of_twl_list)
    qed
  show "twl_clause (swap_lit C j k) =
    TWL_Clause ({#the (lit_lookup C k)#} + remove1_mset (the (lit_lookup C j)) (wf_watched C))
     ({#the (lit_lookup C j)#} + remove1_mset (the (lit_lookup C k)) (wf_unwatched C))"
    if "j \<in># wf_watched_lits C" and "k \<in># wf_unwatched_lits C"
    for C :: "'a literal wf_clause_RBT" and j k :: lit
    using twl_clause_swap_lit that by fast
qed


subsection \<open>Definition of the Clauses\<close>

subsubsection \<open>Definition and Lifting\<close>
typedef 'v RBT_array  =
  "{C :: (nat, 'v) RBT.rbt. RBT.keys C = [0..< length (RBT.keys C)]}"
  morphisms conc_RBT_array abs_RBT_array
proof
  show "RBT.empty \<in> ?RBT_array"
    by auto
qed

definition RBT_delete_and_move :: "nat \<Rightarrow> (nat, 'b) RBT.rbt \<Rightarrow> (nat, 'b) RBT.rbt"  where
"RBT_delete_and_move k C =
  List.foldr
    (\<lambda>(i, C) D. if i < k then RBT.insert i C D else if i = k then D else RBT.insert (i-1) C D)
    (RBT.entries C)
    RBT.empty"

lemma RBT_delete_and_move_empty[simp]: "RBT_delete_and_move k RBT.empty = RBT.empty"
  by (auto simp: RBT_delete_and_move_def)

lemma lookup_filter_aux:
  fixes k :: nat
  shows
    "RBT.lookup
      (List.foldr
         ((\<lambda>(i, C) D. if i < k then RBT.insert i C D
         else if i = k then D else RBT.insert (i-1) C D))
       xs t) i =
      (if i < k
      then case map_of xs i of
          None \<Rightarrow> RBT.lookup t i
        | Some v \<Rightarrow> Some v
      else case map_of xs (i+1) of
          None \<Rightarrow> RBT.lookup t i
        | Some v \<Rightarrow> Some v)"
proof -
  show ?thesis
    proof (induction xs arbitrary: )
      case Nil
      then show ?case by auto
    next
      case (Cons x xs)
      then show ?case
        by (cases x) auto
    qed
qed

lemma RBT_lookup_RBT_delete_and_move:
  "RBT.lookup (RBT_delete_and_move k C) i
    = (if i < k then RBT.lookup C i else RBT.lookup C (i+1))"
  unfolding RBT_delete_and_move_def
  by (auto simp: lookup_filter_aux split: option.splits)

lemma sorted_sorted_map_move:
  fixes xs :: "nat list"
  shows "sorted xs \<Longrightarrow> sorted (map (\<lambda>i. if k < i then i - 1 else i) xs)"
proof (induction rule: sorted.induct)
  case Nil
  then show ?case
    by auto
next
  case (Cons xs x)
  then show ?case
    by (force intro!: sorted.intros)
qed

lemma distinct_distinct_map_move:
  fixes xs :: "nat list"
  shows "k \<notin> set xs \<Longrightarrow> distinct xs \<Longrightarrow> distinct (map (\<lambda>i. if k < i then i - 1 else i) xs)"
  apply (induction xs)
    apply auto[]
   apply (auto dest: less_imp_Suc_add)[]
  using less_Suc_eq by fastforce

lemma in_fst_RBT_entries:
  "a \<in> fst ` set (RBT.entries C) \<longleftrightarrow> RBT.lookup C a \<noteq> None"
  by (force simp: lookup_in_tree)

lemma sorted_removeAll: "sorted C \<Longrightarrow> sorted (removeAll k C)"
  by (metis map_ident removeAll_filter_not_eq sorted_filter)

lemma sorted_distinct_removeAll_insort:
  assumes "sorted C" and "distinct C" and "k' \<notin> set C"
  shows "removeAll k (insort k' C) = (if k = k' then removeAll k C else insort k' (removeAll k C))"
  apply (rule sorted_distinct_set_unique)
  using assms by (auto simp: set_insort sorted_insort sorted_removeAll distinct_removeAll
    distinct_insort)

lemma RBT_keys_eq_iff_dom_eq: "RBT.keys C = RBT.keys D \<longleftrightarrow> dom (RBT.lookup C) = dom (RBT.lookup D)"
  by (metis RBT.distinct_keys finite_dom_lookup finite_sorted_distinct_unique lookup_keys
    sorted_keys)

lemma RBT_keys_RBT_delete_and_move_RBT_insert:
  "RBT.keys (RBT_delete_and_move k (RBT.insert k v C)) =  RBT.keys (RBT_delete_and_move k C)"
  by (auto simp: RBT_keys_eq_iff_dom_eq RBT_lookup_RBT_delete_and_move)

lemma RBT_keys_delete_and_move_insert:
  "RBT.keys (RBT_delete_and_move k (RBT.insert k' v C)) =
  (if k' = k then RBT.keys (RBT_delete_and_move k C)
  else if k' < k then RBT.keys (RBT.insert k' v (RBT_delete_and_move k C))
  else RBT.keys (RBT.insert (k' - 1) v (RBT_delete_and_move k C)))"
  by (auto simp: RBT_keys_RBT_delete_and_move_RBT_insert
    RBT_keys_eq_iff_dom_eq RBT_lookup_RBT_delete_and_move
    split: if_splits)

lemma removeAll_insert_removeAll: "removeAll k (insort k xs) = removeAll k xs"
  by (simp add: filter_insort_triv removeAll_filter_not_eq)

lemma filter_sorted: "sorted xs \<Longrightarrow> sorted (filter P xs)"
  by (metis list.map_ident sorted_filter)

lemma removeAll_insort:
  "sorted xs \<Longrightarrow> k \<noteq> k' \<Longrightarrow> removeAll k' (insort k xs) = insort k (removeAll k' xs)"
  by (simp add: filter_insort removeAll_filter_not_eq)

lemma RBT_keys_RBT_delete_and_move:
  "RBT.keys (RBT_delete_and_move k C) =
    map (\<lambda>i. if i > k then (i - 1) else i) (removeAll k (RBT.keys C))"
proof (induct C rule: rbt_induct)
  case (independancy S T)
  then show ?case using independancy
    by (simp add: RBT_delete_and_move_def keys_def_alt entries_lookup[symmetric])
next
  case empty
  show ?case
    by (simp add: RBT_delete_and_move_def keys_def_alt entries_lookup[symmetric])
next
  case (insert k' v' C) note min = this(1) and IH = this(2)
  let ?k' = "if k' \<le> k then k' else k' - 1"
  have H[simp]: "map (\<lambda>i. if k < i then i - 1 else i) (insort k' xs) =
    ?k' # (map (\<lambda>i. if k < i then i - 1 else i) xs)"
    if "\<forall>k'a\<in>set xs. k' < k'a" for xs
    apply (subst insort_is_Cons)
      using that apply auto[]
     apply auto[]
    done
  have [simp]: "remove1 k' (removeAll k (RBT.keys C)) = removeAll k' (removeAll k (RBT.keys C))"
    by (simp add: distinct_remove1_removeAll distinct_removeAll)
  have removeAll_map:
    "removeAll (k'::nat) (map (\<lambda>i. if k < i then i - 1 else i) (removeAll k xs)) =
      map (\<lambda>i. if k < i then i - 1 else i) (removeAll (if k \<le> k' then k'+1 else k')
         (removeAll k xs))" for k' xs
    by (induction xs) auto
  have remove1_map:
    "remove1 (k'::nat) (map (\<lambda>i. if k < i then i - 1 else i) (removeAll k xs)) =
      map (\<lambda>i. if k < i then i - 1 else i) (remove1 (if k \<le> k' then k'+1 else k')
         (removeAll k xs))" for k' xs
    by (induction xs) auto
  have [simp]: "remove1 k' (map (\<lambda>i. if k < i then i - 1 else i) (removeAll k (RBT.keys C))) =
    removeAll k' (map (\<lambda>i. if k < i then i - 1 else i) (removeAll k (RBT.keys C)))"
    by (metis IH RBT.distinct_keys distinct_remove1_removeAll)
  have insort_map[simp]: "insort k' (map (\<lambda>i. if k < i then i - 1 else i)
       xs) =
    k' # (map (\<lambda>i. if k < i then i - 1 else i) xs)"
    if " \<forall>k'a\<in>set xs. k' < k'a" for k' xs
    apply (rule insort_is_Cons)
    using that by auto
  show ?case using min
    apply (auto simp:  RBT_keys_insert_insort IH
      distinct_remove1_removeAll
      RBT_keys_delete_and_move_insert
      removeAll_insert_removeAll removeAll_insort sorted_removeAll
      remove1_map)
    apply (subst insort_map)
    apply auto
    done
qed

lemma length_RBT_entries_keys:
  "length (RBT.entries C) = length (RBT.keys C)"
  by (simp add: keys_def_alt)

lemma RBT_lookup_Some_in_keysD:
  "RBT.lookup C k = Some a \<Longrightarrow> k \<in> set (RBT.keys C)"
  by (simp add: in_RBT_keys_lookup)

lemma length_RBT_entries_RBT_delete_and_move: "length (RBT.entries (RBT_delete_and_move k C)) =
  (if RBT.lookup C k \<noteq> None then length (RBT.entries C) - 1 else length (RBT.entries C))"
  by (auto simp: RBT_keys_RBT_delete_and_move length_RBT_entries_keys
    length_remove1 distinct_remove1_removeAll[symmetric] in_RBT_keys_lookup
    dest: RBT_lookup_Some_in_keysD)

setup_lifting type_definition_RBT_array
lift_definition cls_lookup :: "'v RBT_array \<Rightarrow> nat \<Rightarrow> 'v option" is RBT.lookup .
lift_definition cls_keys :: "'v RBT_array \<Rightarrow> nat multiset" is
"\<lambda>Cs :: (nat, 'v) RBT.rbt. mset (RBT.keys Cs)" .
lift_definition cls_entries :: "'v RBT_array \<Rightarrow> (nat \<times> 'v) list" is RBT.entries .
lift_definition cls_empty :: "'v RBT_array" is RBT.empty by auto
lift_definition cls_length :: "'v RBT_array \<Rightarrow> nat" is "\<lambda>C. length (RBT.keys C)" .

lemma count_mset_count_list:
  "count (mset xs) x = count_list xs x"
  by (induction xs) auto

lemma length_removeAll_count_list:
  "length (removeAll x xs) = length xs - count_list xs x"
proof -
  have "length (removeAll x xs) = size (removeAll_mset x (mset xs))"
    by auto
  also have "\<dots> = size (mset xs) - count (mset xs) x"
    by (metis count_le_replicate_mset_le le_refl size_Diff_submset size_replicate_mset)
  also have " \<dots> = length xs - count_list xs x"
    unfolding count_mset_count_list by simp
  finally show ?thesis .
qed

lemma removeAll_upt:
  "removeAll k [a..<b] = (if k \<ge> a \<and> k < b then [a..<k] @ [Suc k..<b] else [a..<b])"
  by (induction b) auto

lemma remove1_upt:
  "remove1 k [a..<b] = (if k \<ge> a \<and> k < b then [a..<k] @ [Suc k..<b] else [a..<b])"
  by (subst distinct_remove1_removeAll) (auto simp: removeAll_upt)

lift_definition cls_delete :: "nat \<Rightarrow> 'v RBT_array  \<Rightarrow> 'v RBT_array" is RBT_delete_and_move
proof -
  fix C :: "(nat, 'v) RBT.rbt" and k :: nat
  assume wf: "RBT.keys C = [0..<length (RBT.keys C)]"
  have le_keys_lookup:  "k < length (RBT.keys C) \<longleftrightarrow> RBT.lookup C k \<noteq> None" for k :: nat
    unfolding in_RBT_keys_lookup[symmetric] by (subst wf) auto
  have [simp]: "length (RBT.keys (RBT_delete_and_move k C)) =
    length (RBT.keys C) - (if k < length (RBT.keys C) then 1 else 0)"
     by (subst wf) (auto simp: RBT_keys_RBT_delete_and_move length_removeAll_count_list
      count_mset_count_list[symmetric] count_RBT_keys le_keys_lookup)
  have [simp]: "map (\<lambda>i. if k < i then i - 1 else i) [0..<a] = [0..<a]"
    if "a \<le> k" for a :: nat
    using that by (induction a) auto
  have [simp]: "map (\<lambda>i. if k < i then i - 1 else i) [a..<b] = [a-1..<b-1]"
    if "a > 0" and "a > k" for a b :: nat
    using that apply (induction b)
      apply simp
    by (case_tac b) (auto split: if_splits intro: append_cons_eq_upt_length_i)
  have upt_cut: "[0..<k] @ [k..<length (RBT.keys C) - Suc 0] = [0..<length (RBT.keys C) - Suc 0]"
    if "k < length (RBT.keys C)"
    by (metis that One_nat_def diff_Suc_1 leI less_imp_Suc_add not_less0 upt_add_eq_append)

  show "RBT.keys (RBT_delete_and_move k C) = [0..<length (RBT.keys (RBT_delete_and_move k C))]"
    by (subst RBT_keys_RBT_delete_and_move, subst wf) (auto simp: removeAll_upt upt_cut)
qed

fun clss_update_safe where
"clss_update_safe Cs i C =
  (case RBT.lookup Cs i of
    None \<Rightarrow> Cs
  | Some _ \<Rightarrow> RBT.insert i C Cs)
"

lift_definition clss_update :: "'v RBT_array \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'v RBT_array" is clss_update_safe
proof -
  fix C :: "(nat, 'v) RBT.rbt" and k :: nat and v :: 'v
  define u where u: "u = length (RBT.keys C)"
  assume wf: "RBT.keys C = [0..<length (RBT.keys C)]"
  have insort_remove_upt:
    "insort k (remove1 k [0..<u])  = (if k < u then [0..<u] else [0..<u] @ [k])"
    apply (cases "k < u")
    apply (subst insort_remove1)
       apply auto[3]
    apply (rule sorted_distinct_set_unique)
    by (auto simp: sorted_distinct_set_unique  remove1_upt sorted_insort distinct_insort
      set_insort sorted_append)

  have False if
    "RBT.keys C = [0..<length (RBT.keys C)]" and
    "\<not> k < length (RBT.keys C)" and
    " RBT.lookup C k = Some i" for i
    using that
    by (metis RBT.keys_entries atLeastLessThan_iff lookup_in_tree set_upt)
  then show "RBT.keys (clss_update_safe C k v) =
    [0..<length (RBT.keys (clss_update_safe C k v))]"
    using wf by (auto split: option.splits simp: mset_RBT_keys_insert RBT_keys_insert_insort
    atLeastLessThanSuc insort_remove1 lookup_in_tree u[symmetric]
    insort_remove_upt)
qed

definition RBT_append :: "(nat, 'v) RBT.rbt \<Rightarrow> 'v \<Rightarrow> (nat, 'v) RBT.rbt \<times> nat" where
"RBT_append Cs C =
  (let i = length (RBT.keys Cs) in
    (RBT.insert i C Cs, i))"

text \<open>@{thm insort_is_Cons} is more general.\<close>
lemma insort_is_append: "\<forall>x\<in>set xs. a \<ge> x \<Longrightarrow> sorted xs \<Longrightarrow> insort a xs = xs @ [a]"
by (induction xs) (auto simp add: insort_is_Cons sorted_Cons)

text \<open>See @{thm sorted_distinct_set_unique}.\<close>
lemma sorted_mset_unique:
  fixes xs :: "'a :: linorder list"
  shows "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> mset xs = mset ys \<Longrightarrow> xs = ys"
  using properties_for_sort by auto

lemma insort_upt: "insort k [a..<b] =
  (if k < a then k # [a..<b]
  else if k < b then [a..<k] @ k # [k ..<b]
  else [a..<b] @[k])"
proof -
  have H: "k < Suc b \<Longrightarrow> \<not> k < a \<Longrightarrow> {a..<b} = {a..<k} \<union> {k..<b}" for a b :: nat
    by (simp add: ivl_disj_un_two(3))
  show ?thesis

  apply (induction b)
   apply simp
  apply (case_tac "\<not>k < a \<and> k < Suc b")
   apply (rule sorted_mset_unique)
      apply (auto simp add: sorted_append sorted_insort sorted_Cons ac_simps mset_set_Union
        dest!: H)[4]
    apply (auto simp: insort_is_Cons insort_is_append sorted_append)
  done
qed

lemma RBT_lookup_fst_RBT_append:
  "RBT.lookup (fst (RBT_append Cs C)) = (RBT.lookup Cs) (length (RBT.keys Cs) \<mapsto> C)"
  by (auto simp: Let_def RBT_append_def)

lift_definition add_cls :: "'v RBT_array \<Rightarrow> 'v \<Rightarrow> 'v RBT_array \<times> nat" is RBT_append
proof -
  fix C :: "(nat, 'v) RBT.rbt" and v :: 'v
  define u where u: "u = length (RBT.keys C)"
  assume wf: "RBT.keys C = [0..<length (RBT.keys C)]"
  have [simp]: "remove1 u [0..<u] = RBT.keys C"
    by (metis wf nat_neq_iff remove1_upt u)
  show "pred_prod (\<lambda>C. RBT.keys C = [0..<length (RBT.keys C)]) top (RBT_append C v)"
    using wf by (auto simp: Let_def mset_RBT_keys_insert length_RBT_keys_insert ac_simps
    RBT_append_def RBT_keys_insert_insort u[symmetric] insort_upt)
qed

lemma conc_RBT_array_fst_add_cls_rep_eq:
  "conc_RBT_array (fst (add_cls Cs C)) = fst (RBT_append (conc_RBT_array Cs) C)"
  by (metis add_cls.rep_eq apfst_def fst_apfst)

lemma cls_lookup_fst_add_cls:
  "cls_lookup (fst (add_cls Cs C)) = (cls_lookup Cs) (cls_length Cs \<mapsto> C)"
  by (auto simp: RBT_lookup_fst_RBT_append conc_RBT_array_fst_add_cls_rep_eq
    cls_length.rep_eq cls_lookup.rep_eq)


subsubsection \<open>Instantiations\<close>

interpretation RBT: abstract_clauses_representation where
  cls_lookup = cls_lookup and
  cls_keys = cls_keys and
  add_cls = add_cls and
  clss_update = clss_update
  apply unfold_locales
     apply (auto simp: keys_entries lookup_in_tree cls_keys.rep_eq)[]
    apply (auto simp: keys_entries lookup_in_tree cls_keys.rep_eq
      cls_lookup.rep_eq)[]
    apply (auto simp: keys_entries lookup_in_tree[symmetric] cls_keys.rep_eq
      cls_lookup.rep_eq clss_update.rep_eq split: option.splits)[]
    (* TODO tune proof *)
   apply (auto simp: keys_entries lookup_in_tree[symmetric] cls_keys.rep_eq
     cls_lookup.rep_eq clss_update.rep_eq add_cls.rep_eq add_cls_def Let_def
     RBT_append_def
     split: option.splits)[]
apply (metis (mono_tags, lifting) atLeastLessThan_iff conc_RBT_array domI lookup_keys
  mem_Collect_eq not_le order_refl set_mset_mset set_upt )
   apply (auto simp: keys_entries lookup_in_tree[symmetric] cls_keys.rep_eq
     cls_lookup.rep_eq clss_update.rep_eq add_cls.rep_eq add_cls_def Let_def RBT_append_def
     split: option.splits)[]
by (metis (mono_tags, lifting) atLeastLessThan_iff conc_RBT_array domI less_irrefl
  lookup_keys mem_Collect_eq set_mset_mset set_upt)

interpretation RBT: abstract_clause_clauses_representation where
  wf_watched_lits = "wf_watched_lits :: 'v literal wf_clause_RBT \<Rightarrow> lit multiset" and
  wf_unwatched_lits = wf_unwatched_lits and
  lit_lookup = lit_lookup and
  lit_keys = lit_keys and
  swap_lit = swap_lit and
  it_of_watched_ordered = it_of_watched_ordered and
  cls_of_twl_list = "cls_of_twl_list :: 'v literal list \<Rightarrow> 'v literal wf_clause_RBT" and
  cls_lookup = cls_lookup and
  cls_keys = cls_keys and
  add_cls = add_cls and
  clss_update = clss_update
  by unfold_locales

interpretation RBT: raw_cls mset
  by unfold_locales

interpretation RBT: abs_state\<^sub>W_clss_twl_ops where
  wf_watched_lits = "wf_watched_lits :: 'v literal wf_clause_RBT \<Rightarrow> lit multiset" and
  wf_unwatched_lits = wf_unwatched_lits and
  lit_lookup = lit_lookup and
  lit_keys = lit_keys and
  swap_lit = swap_lit and
  it_of_watched_ordered = it_of_watched_ordered and
  cls_of_twl_list = "cls_of_twl_list :: 'v literal list \<Rightarrow> 'v literal wf_clause_RBT" and
  cls_lookup = cls_lookup and
  cls_keys = cls_keys and
  add_cls = add_cls and
  clss_update = clss_update and
  mset_ccls = mset
  by unfold_locales


fun map_on_annot :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c, 'a) ann_lit \<Rightarrow> ('c, 'b) ann_lit" where
"map_on_annot f (Propagated L C) = Propagated L (f C)" |
"map_on_annot _ (Decided L) = Decided L"


subsection \<open>Definition of the State\<close>

type_synonym keys = nat
datatype 'v w =
  W (raw_prop_trail: "('v, keys) ann_lits")
    (raw_trail: "('v, keys) ann_lits")
    (clss: "'v literal wf_clause_RBT RBT_array")
    (starting_learned_clause_index: nat)
    (backtrack_lvl: nat)
    (raw_conflicting: "'v literal list option")

abbreviation full_trail :: "'a w \<Rightarrow> ('a, nat) ann_lit list" where
"full_trail S \<equiv> raw_prop_trail S @ raw_trail S"

fun valid_annotation :: "'v literal wf_clause_RBT RBT_array \<Rightarrow> ('b, keys) ann_lit \<Rightarrow> bool"  where
"valid_annotation Cs (Propagated _ E) \<longleftrightarrow> cls_lookup Cs E \<noteq> None" |
"valid_annotation Cs (Decided _) \<longleftrightarrow> True"

lemma valid_annotation_cases:
  "valid_annotation Cs L = (case L of Propagated _ E \<Rightarrow> cls_lookup Cs E \<noteq> None | _ \<Rightarrow> True)"
  by (cases L) auto

definition valid_annotations :: "'a w \<Rightarrow> ('b, keys) ann_lits \<Rightarrow> bool" where
"valid_annotations S M \<longleftrightarrow>
   (\<forall>C \<in> set M. valid_annotation (clss S) C)"

abbreviation valid_annot where
"valid_annot S \<equiv> valid_annotations S (full_trail S)"

lemma valid_annotations_tl: "valid_annotations S M \<Longrightarrow> valid_annotations S (tl M)"
  unfolding valid_annotations_def
  by (cases M) auto

lemma valid_annotations_cons[simp]:
  "valid_annotations S (L # M) \<longleftrightarrow> valid_annotation (clss S) L \<and> valid_annotations S M"
  by (auto simp: valid_annotations_def)

lemma valid_annotations_append[simp]:
  "valid_annotations S (M' @ M) \<longleftrightarrow> valid_annotations S M' \<and> valid_annotations S M"
  by (auto simp: valid_annotations_def)

typedef 'v wf_state = "{S :: 'v w. valid_annot S}"
proof
  show "W [] [] cls_empty 0 0 None \<in> ?wf_state"
    by (auto simp: valid_annotations_def)
qed

definition learned_clauses_w :: "'a w \<Rightarrow> 'a literal multiset multiset" where
"learned_clauses_w S =
  mset (map (wf_RBT_clause o snd)
    (filter (\<lambda>(k, _). k \<ge> (starting_learned_clause_index S)) (cls_entries (clss S))))"

setup_lifting type_definition_wf_state
lift_definition abs_trail :: "'v wf_state \<Rightarrow> ('v, keys) ann_lits" is raw_trail .
lift_definition prop_queue :: "'v wf_state \<Rightarrow> ('v, keys) ann_lits" is raw_prop_trail .
lift_definition hd_raw_abs_trail :: "'v wf_state \<Rightarrow> ('v, keys) ann_lit" is
"\<lambda>S. hd (raw_prop_trail S @ raw_trail S)" .
lift_definition raw_clauses :: "'v wf_state \<Rightarrow> 'v literal wf_clause_RBT RBT_array" is clss .
lift_definition abs_backtrack_lvl :: "'v wf_state \<Rightarrow> nat" is backtrack_lvl .
lift_definition raw_conc_conflicting :: "'v wf_state \<Rightarrow> 'v literal list option" is raw_conflicting .
lift_definition abs_learned_clss :: "'v wf_state \<Rightarrow> 'v clauses" is learned_clauses_w .

definition tl_trail :: "'v w \<Rightarrow>'v w" where
"tl_trail S =
  (if raw_prop_trail S \<noteq> []
  then
    W
    (tl (raw_prop_trail S))
    (raw_trail S)
    (clss S)
    (starting_learned_clause_index S)
    (backtrack_lvl S)
    (raw_conflicting S)
  else
    W
    (raw_prop_trail S)
    (tl (raw_trail S))
    (clss S)
    (starting_learned_clause_index S)
    (backtrack_lvl S)
    (raw_conflicting S))"

lemma full_trail_tl_trail[simp]: "full_trail (tl_trail S) = tl (full_trail S)"
  by (auto simp: tl_trail_def tl_append split: list.split)

lemma
  clss_tl_trail[simp]: "clss (tl_trail S) = clss S" and
  backtrack_lvl_tl_trail[simp]: "backtrack_lvl (tl_trail S) = backtrack_lvl S"
  by (auto simp: tl_trail_def)

lift_definition tl_abs_trail :: "'v wf_state \<Rightarrow> 'v wf_state" is tl_trail
  by (metis clss_tl_trail full_trail_tl_trail valid_annotations_def valid_annotations_tl)

definition raw_cons_prop_queue :: "('v, keys) ann_lit \<Rightarrow> 'v w \<Rightarrow>'v w" where
  "raw_cons_prop_queue L S = W (L # raw_prop_trail S)
    (raw_trail S) (clss S)
    (starting_learned_clause_index S)
    (backtrack_lvl S)
    (raw_conflicting S)"

lemma clss_raw_cons_prop_queue[simp]:
  "clss (raw_cons_prop_queue L S) = clss S"
  by (auto simp: raw_cons_prop_queue_def)

lemma valid_annotations_raw_cons_prop_queue[iff]:
  "valid_annotations (raw_cons_prop_queue L S) M \<longleftrightarrow> valid_annotations S M"
  by (simp add: valid_annotations_def)

lift_definition cons_prop_queue :: "('v, keys) ann_lit \<Rightarrow> 'v wf_state \<Rightarrow> 'v wf_state" is
"\<lambda>(L::('v, nat) ann_lit) S. if valid_annotation (clss S) L then raw_cons_prop_queue L S else S"
  by (auto simp: raw_cons_prop_queue_def valid_annotations_def)

definition find_undef_in_unwatched :: "'v w \<Rightarrow> 'v literal wf_clause_RBT \<Rightarrow> lit option"  where
"find_undef_in_unwatched S C =
  map_option fst
    (find (\<lambda>(k, C). k \<ge> 2 \<and> undefined_lit (raw_trail S @ raw_prop_trail S) C)
          (lit_entries C))"

lift_definition abs_find_undef_in_unwatched :: "'v wf_state \<Rightarrow> 'v literal wf_clause_RBT \<Rightarrow> lit option"  is
 find_undef_in_unwatched .

lemma find_undef_in_unwatched:
  fixes k :: lit and C :: "'v literal wf_clause_RBT"
  assumes "find_undef_in_unwatched S C = Some k"
  shows "k \<in># wf_unwatched_lits C" and "lit_lookup C k \<noteq> None" and
    "undefined_lit (raw_trail S @ raw_prop_trail S) (the (lit_lookup C k))"
proof -
  obtain L :: "'v literal" and i :: nat where
    "k \<ge> 2" and
    i: "i < length (RBT.entries (conc_RBT_cls C))" and
    entries: "RBT.entries (conc_RBT_cls C) ! i = (k, L)" and
    undef: "undefined_lit (raw_trail S @ raw_prop_trail S) L"
    using assms by (auto simp: find_undef_in_unwatched_def
      lit_entries.rep_eq lookup_in_tree
      find_Some_iff)
  have kL: "(k, L) \<in> set (lit_entries C)"
    using i entries by (auto simp: lit_lookup.rep_eq lookup_in_tree lit_entries.rep_eq dest: nth_mem)
  then show "lit_lookup C k \<noteq> None"
    by (auto simp: lit_lookup.rep_eq lookup_in_tree lit_entries.rep_eq)
  show "k \<in># wf_unwatched_lits C"
    using kL \<open>k \<ge> 2 \<close> by (auto simp: lit_lookup.rep_eq get_unwatched_lits_def
      wf_unwatched_lits.rep_eq lit_entries.rep_eq keys_entries)
  show "undefined_lit (raw_trail S @ raw_prop_trail S) (the (lit_lookup C k))"
    using undef kL by (simp add: lookup_in_tree[symmetric] lit_entries.rep_eq lit_lookup.rep_eq)
qed

fun reduce_trail_to :: "'a list \<Rightarrow> 'b w \<Rightarrow> 'b w"  where
"reduce_trail_to M' (W P M Cs l k C) =
  (if P = [] then W [] (drop (length M - length M') M) Cs l k C
  else (W P M Cs l k C))"

lift_definition reduce_abs_trail_to :: "'a list \<Rightarrow> 'v wf_state \<Rightarrow> 'v wf_state" is reduce_trail_to
  by (case_tac w) (metis (no_types, lifting) append_self_conv2 in_set_dropD reduce_trail_to.simps
   valid_annotations_def w.sel(1) w.sel(2) w.sel(3))

primrec last_prop_queue_to_trail :: "'a w \<Rightarrow> 'a w"  where
"last_prop_queue_to_trail (W P M Cs l k C) =
  (case P of
    [] \<Rightarrow> W P M Cs l k C
  | _ \<Rightarrow> W (butlast P) (last P # M) Cs l k C)"

lift_definition last_prop_queue_to_abs_trail :: "'v wf_state \<Rightarrow> 'v wf_state" is
  last_prop_queue_to_trail
  by (case_tac w) (auto simp: valid_annotations_def split: list.splits dest: in_set_butlastD)

primrec prop_queue_to_trail :: "'a w \<Rightarrow> 'a w" where
"prop_queue_to_trail (W P M Cs l k C) = W [] (P @ M) Cs l k C"

lift_definition prop_queue_to_abs_trail :: "'v wf_state \<Rightarrow> 'v wf_state" is
  prop_queue_to_trail
  by (case_tac w) (auto simp: valid_annotations_def)

primrec add_confl_to_learned_cls :: "'a w \<Rightarrow> 'a w" where
"add_confl_to_learned_cls (W P M Cs l k C) =
  (case C of
    None \<Rightarrow> W P M Cs l k None
  | Some C \<Rightarrow> W P M (fst (add_cls Cs (cls_of_twl_list C))) l k None)"

lift_definition add_abs_confl_to_learned_cls :: "'v wf_state \<Rightarrow> 'v wf_state" is
  add_confl_to_learned_cls
  by (case_tac w) (auto simp: valid_annotations_def valid_annotation_cases cls_lookup_fst_add_cls
    split: option.splits ann_lit.splits)

fun remove_first where
"remove_first _ [] = []" |
"remove_first C (C' # L) = (if mset C = mset C' then L else C' # remove_first C L)"

lemma mset_map_mset_remove_first:
  "mset (map mset (remove_first a C)) = remove1_mset (mset a) (mset (map mset C))"
  by (induction C) (auto simp: ac_simps remove1_mset_single_add)
(*
interpretation abstract_clause_representation_ops where
  lit_lookup = RBT.lookup and
  lit_keys = RBT.entries and
  twl_cls = id and
  swap_lit = swap_lit and
  it_of_watched_ordered = "\<lambda>i. case i of 0 \<Rightarrow> 1 | 1 \<Rightarrow> 0" and
  cls_of_twl_list = id

interpretation abs_state\<^sub>W_clss_twl_ops
  "\<lambda>L i. mset (the (L ! i))"
  "\<lambda>L. mset (map mset (map the (filter (op \<noteq> None) L)))"
  "\<lambda>i C. i < length C \<and> C ! i \<noteq> None"

  mset
  "\<lambda>S i. the (S ! i)"
  "\<lambda>S Cs L C. remdups (remove1 (-L) (the (raw_conflicting S)) @ remove1 L (the (Cs ! C)))"
  "\<lambda>S. map (map_on_annot (\<lambda>i. mset (the ((raw_init_clss S @ raw_learned_clss S) ! i))))
         (raw_trail S)"
  "\<lambda>S. hd (raw_trail S)"
  "\<lambda>S. raw_init_clss S @ raw_learned_clss S"
  backtrack_lvl
  raw_conflicting
  "\<lambda>S. mset (map mset (map the (filter (op \<noteq> None) (raw_learned_clss S))))"
  "\<lambda>L S. W (L # raw_trail S) (raw_init_clss S) (raw_learned_clss S) (backtrack_lvl S)
    (raw_conflicting S)"
  "\<lambda>S. W (tl (raw_trail S)) (raw_init_clss S) (raw_learned_clss S) (backtrack_lvl S)
    (raw_conflicting S)"
  "\<lambda>S. W (raw_trail S) (raw_init_clss S) (raw_learned_clss S @ [raw_conflicting S])
    (backtrack_lvl S) (raw_conflicting S)"
  "\<lambda>i S. W (raw_trail S) (list_update (raw_init_clss S) i None)
    (list_update (raw_learned_clss S) i None)
    (backtrack_lvl S) (raw_conflicting S)"
  "\<lambda>k S. W (raw_trail S) (raw_init_clss S) (raw_learned_clss S) k
    (raw_conflicting S)"
  "\<lambda>C S. W (raw_trail S) (raw_init_clss S) (raw_learned_clss S) (backtrack_lvl S)
    C"
  "\<lambda>N. W [] N [] 0 None"
  "id"

proof (unfold_locales, goal_cases)
  case (1 i l)
  then have "l ! i \<in> {x \<in> set l. x \<noteq> None}"
    using List.nth_mem by (auto simp: comp_def)
  then show ?case
    by (auto simp: comp_def)
next
  case (2 b l)
  then obtain i b' where
    "l ! i = Some b'" and
    "i < length l"
    "b = mset b'"
    apply auto
    apply (case_tac x)
    by (auto simp: in_set_conv_nth)
  then show ?case by auto
qed auto

declare RBT_CDCL_W.mset_ccls_ccls_of_cls[simp del]
interpretation state\<^sub>W
  "\<lambda>L i. mset (the (L ! i))"
  "\<lambda>L. mset (map mset (map the (filter (op \<noteq> None) L)))"
  "\<lambda>i C. i < length C \<and> C ! i \<noteq> None"

  mset
  "\<lambda>S i. the (S ! i)"
  "\<lambda>S Cs L C. remdups (remove1 (-L) (the (raw_conflicting S)) @ remove1 L (the (Cs ! C)))"
  "\<lambda>S. map (map_on_annot (\<lambda>i. mset (the ((raw_init_clss S @ raw_learned_clss S) ! i))))
         (raw_trail S)"
  "\<lambda>S. hd (raw_trail S)"
  "\<lambda>S. raw_init_clss S @ raw_learned_clss S"
  backtrack_lvl
  raw_conflicting
  "\<lambda>S. mset (map mset (map the (filter (op \<noteq> None) (raw_learned_clss S))))"
  "\<lambda>L S. W (L # raw_trail S) (raw_init_clss S) (raw_learned_clss S) (backtrack_lvl S)
    (raw_conflicting S)"
  "\<lambda>S. W (tl (raw_trail S)) (raw_init_clss S) (raw_learned_clss S) (backtrack_lvl S)
    (raw_conflicting S)"
  "\<lambda>S. W (raw_trail S) (raw_init_clss S) (raw_learned_clss S @ [raw_conflicting S])
    (backtrack_lvl S) (raw_conflicting S)"
  "\<lambda>i S. W (raw_trail S) (list_update (raw_init_clss S) i None)
    (list_update (raw_learned_clss S) i None)
    (backtrack_lvl S) (raw_conflicting S)"
  "\<lambda>k S. W (raw_trail S) (raw_init_clss S) (raw_learned_clss S) k
    (raw_conflicting S)"
  "\<lambda>C S. W (raw_trail S) (raw_init_clss S) (raw_learned_clss S) (backtrack_lvl S)
    C"
  "\<lambda>N. W [] N [] 0 None"
  "\<lambda>S. W [] (raw_init_clss S) [] 0 None"

  apply unfold_locales
  prefer 47 apply simp
  prefer 46 apply simp
  prefer 45 apply simp
  prefer 44 apply (simp del: List.map_map add: init_clss_def)
  prefer 43 apply simp
  prefer 42 apply simp
  prefer 41 apply simp
  prefer 40 apply simp
  prefer 39 apply (simp del: List.map_map add: init_clss_def)
  prefer 38 apply simp

  apply (auto simp: comp_def ac_simps)
  apply (auto simp: comp_def hd_map map_tl ac_simps)
  defer defer defer defer
  apply (auto simp: clauses_init_learned comp_def ac_simps nth_append)[2]
  defer
  apply (auto simp: comp_def ac_simps)
  thm nth_append
  done
  oops

by (simp add: nth_append)
interpretation state\<^sub>W
  "\<lambda>L i. mset (the (RBT.lookup L i)) :: 'v clause"
  "\<lambda>L. mset (map (\<lambda>L. mset (snd L)) (RBT.entries L)) :: 'v clauses"
  "\<lambda>i L. RBT.lookup L i \<noteq> None"
  "\<lambda>i C. RBT.delete i C"

  mset
  "\<lambda>L i. the (RBT.lookup L i)"
  "\<lambda>S Cs L C. remdups (remove1 (-L) (the (raw_conflicting (Conc S)))
    @ remove1 L (the (RBT.lookup Cs C)))"
  "\<lambda>S. map (map_on_annot (\<lambda>i. mset (the (RBT.lookup (RBT.union (raw_init_clss (Conc S))
    (raw_learned_clss (Conc S))) i)))) (raw_trail (Conc S))"
  "\<lambda>S. hd (raw_trail (Conc S)) :: ('v, nat, keys) ann_lit"
  "\<lambda>S. RBT.union (raw_init_clss (Conc S)) (raw_learned_clss (Conc S))"
  "\<lambda>S. backtrack_lvl (Conc S)"
  "\<lambda>S. raw_conflicting (Conc S)"
  "\<lambda>S. mset (map (\<lambda>L. mset (snd L)) (RBT.entries (raw_learned_clss (Conc S))))"
  apply unfold_locales
  apply (case_tac "raw_trail (Conc S)")
  apply (auto simp: comp_def)[10]
  oops



lemma distinct_entries_rbt[simp]: "distinct (RBT.entries C)"
  using distinct_entries[of C] by (metis distinct_zipI1 zip_map_fst_snd)

lemma rbt_impl_of_rbt_Empty:
  "rbt.impl_of (RBT rbt.Empty) = rbt.Empty"
  by (metis empty.abs_eq impl_of_empty)

lemma keys_empty [simp]:
  "RBT.keys RBT.empty = []"
  unfolding RBT.keys_def RBT.empty_def by (auto simp: rbt_impl_of_rbt_Empty)

lemma mset_entries_delete:
  assumes
    ab: "RBT.lookup C a = Some b"
  shows "mset (RBT.entries (RBT.delete a C)) = remove1_mset (a, b) (mset (RBT.entries C))"
proof -
  { fix x y
    have "(x, y) \<in> set (RBT.entries (RBT.delete a C)) \<longleftrightarrow>
    (x, y) \<in> set (RBT.entries C) - {(a, b)}"
      using rbt_delete_in_tree[of "RBT.impl_of C" "x" "y" a] ab
      unfolding lookup_in_tree[symmetric]
      apply (auto split: if_splits simp: lookup_in_tree[symmetric])
      done
  }
  then show ?thesis
    by (auto simp: distinct_mset_remove1_All distinct_removeAll
      set_eq_iff_mset_eq_distinct[symmetric])
qed
abbreviation rbt_values where
"rbt_values C \<equiv> snd ` set (RBT.entries C)"


interpretation list_clss_nth: raw_clss
  "\<lambda>L i. mset (the (RBT.lookup L i))"
  "\<lambda>L. mset (map (\<lambda>L. mset (snd L)) (RBT.entries L))"
  "\<lambda>i L. i \<in> set (RBT.keys L)"
  "\<lambda>i C. RBT.delete i C"
  apply unfold_locales
    apply (auto simp: keys_entries lookup_in_tree[symmetric])[]
    apply (force simp add: lookup_in_tree)[]
  apply (fastforce simp: mset_map mset_entries_delete image_mset_mset_removeAll keys_entries
    lookup_in_tree[symmetric])[]
  apply (fastforce simp: mset_map mset_entries_delete image_mset_mset_removeAll keys_entries
    lookup_in_tree[symmetric])[]
  done

type_synonym keys = nat
datatype 'v map_rbt = MRBT (rbt: "(nat, 'v) RBT_Impl.rbt") (max_index: "nat")

datatype 'v w =
  W (raw_trail: "('v, nat, keys) ann_lits")
    (raw_init_clss: "(keys, 'v literal list) rbt")
    (raw_learned_clss: "(keys, 'v literal list) rbt")
    (backtrack_lvl: nat)
    (raw_conflicting: "'v literal list option")

typedef 'v w_wf = "{S::'v w.
  fst ` set (RBT.entries (raw_init_clss S)) \<subseteq> {0..length (RBT.entries (raw_init_clss S))}}"
morphisms Conc Wf
proof
  show "W [] RBT.empty RBT.empty 0 None \<in> ?w_wf"
  apply (auto simp: RBT.entries_def empty.abs_eq impl_of_empty)
  apply (metis empty.abs_eq empty_iff entries.simps(1) impl_of_empty list.set(1))+
  done
qed

lemma ""
definition tl_trail :: "'v w \<Rightarrow>'v w" where
  "tl_trail S = W (tl (raw_trail S)) (raw_init_clss S)
    (raw_learned_clss S) (backtrack_lvl S)
    (raw_conflicting S)"

lift_definition t :: "'v w_wf \<Rightarrow> 'v w_wf \<rightharpoonup> 'v w_wf" is tl_trail
definition cons_trail :: "('v, nat, keys) ann_lit \<Rightarrow> 'v w_wf \<Rightarrow>'v w_wf" where
  "cons_trail L S = Wf (W (L # raw_trail (Conc S)) (raw_init_clss (Conc S))
    (raw_learned_clss (Conc S)) (backtrack_lvl (Conc S))
    (raw_conflicting (Conc S)))"


locale state\<^sub>W_ops =
  raw_clss mset_cls mset_clss valid_in_clss remove_from_clss
    +
  raw_cls mset_ccls
  for
    -- \<open>Clause\<close>
    mset_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'v clause" and

    -- \<open>Multiset of Clauses\<close>
    mset_clss :: "'clss \<Rightarrow> 'v clauses" and
    valid_in_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> bool"and
    remove_from_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    -- \<open>Conflicting clauses:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause" +
  fixes
    ccls_of_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'ccls" and
    resolve_cls :: "'st \<Rightarrow> 'clss \<Rightarrow> 'v literal \<Rightarrow> 'cls \<Rightarrow> 'ccls" and
    trail :: "'st \<Rightarrow> ('v, nat, 'v clause) ann_lits" and
    hd_raw_trail :: "'st \<Rightarrow> ('v, nat, 'cls) ann_lit" and
    raw_clauses :: "'st \<Rightarrow> 'clss" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conflicting :: "'st \<Rightarrow> 'ccls option" and

    learned_clss :: "'st \<Rightarrow> 'v clauses" and

    cons_trail :: "('v, nat, 'cls) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    confl_to_learned :: "'st \<Rightarrow> 'st" and
    remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'ccls option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st"
  assumes
    mset_ccls_ccls_of_cls[simp]:
      "valid_in_clss C Cs \<Longrightarrow> mset_ccls (ccls_of_cls Cs C) = mset_cls Cs C" and
    mset_ccls_resolve_cls:
      "valid_in_clss C Cs \<Longrightarrow> raw_conflicting S = Some U \<Longrightarrow>
        mset_ccls (resolve_cls S Cs L C) =
          remdups_mset (remove1_mset (-L) (mset_ccls U)
             + remove1_mset L (mset_cls Cs C))" and
    learned_clauses_raw_clauses:
      "learned_clss S \<subseteq># mset_clss (raw_clauses S)"

interpretation state\<^sub>W_ops
  "\<lambda>L i. mset (the (RBT.lookup L i))"
  "\<lambda>L. mset (map (\<lambda>L. mset (snd L)) (RBT.entries L))"
  "\<lambda>i L. i \<in> set (RBT.keys L)"
  "\<lambda>i C. RBT.delete i C"

  mset
  "\<lambda>L i. the (RBT.lookup L i)"
  "\<lambda>S Cs L C. remdups (remove1 (-L) (the (raw_conflicting (Conc S)))
    @ remove1 L (the (RBT.lookup Cs C)))"
  "\<lambda>S. map (map_on_annot (\<lambda>i. mset (the (RBT.lookup (RBT.union (raw_init_clss (Conc S))
    (raw_learned_clss (Conc S))) i)))) (raw_trail (Conc S))"
  "\<lambda>S. hd (raw_trail (Conc S)) :: ('v, nat, keys) ann_lit"
  "\<lambda>S. RBT.union (raw_init_clss (Conc S)) (raw_learned_clss (Conc S))"
  "\<lambda>S. backtrack_lvl (Conc S)"
  "\<lambda>S. raw_conflicting (Conc S)"
  "\<lambda>S. mset (map (\<lambda>L. mset (snd L)) (RBT.entries (raw_learned_clss (Conc S))))"
  apply unfold_locales
  apply (auto simp: )
  sorry

interpretation state\<^sub>W
  "\<lambda>L i. mset (the (RBT.lookup L i)) :: 'v clause"
  "\<lambda>L. mset (map (\<lambda>L. mset (snd L)) (RBT.entries L)) :: 'v clauses"
  "\<lambda>i L. RBT.lookup L i \<noteq> None"
  "\<lambda>i C. RBT.delete i C"

  mset
  "\<lambda>L i. the (RBT.lookup L i)"
  "\<lambda>S Cs L C. remdups (remove1 (-L) (the (raw_conflicting (Conc S)))
    @ remove1 L (the (RBT.lookup Cs C)))"
  "\<lambda>S. map (map_on_annot (\<lambda>i. mset (the (RBT.lookup (RBT.union (raw_init_clss (Conc S))
    (raw_learned_clss (Conc S))) i)))) (raw_trail (Conc S))"
  "\<lambda>S. hd (raw_trail (Conc S)) :: ('v, nat, keys) ann_lit"
  "\<lambda>S. RBT.union (raw_init_clss (Conc S)) (raw_learned_clss (Conc S))"
  "\<lambda>S. backtrack_lvl (Conc S)"
  "\<lambda>S. raw_conflicting (Conc S)"
  "\<lambda>S. mset (map (\<lambda>L. mset (snd L)) (RBT.entries (raw_learned_clss (Conc S))))"
  apply unfold_locales
  apply (case_tac "raw_trail (Conc S)")
  apply (auto simp: comp_def)[10]
  oops
  *)
end