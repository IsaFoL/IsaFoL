theory IsaSAT_Literals
  imports Watched_Literals.Watched_Literals_Watch_List_Domain
     Watched_Literals.Bits_Natural Watched_Literals.WB_Word_Assn
begin


subsubsection \<open>Refinement of the Watched Function\<close>

definition map_fun_rel :: \<open>(nat \<times> 'key) set \<Rightarrow> ('b \<times> 'a) set \<Rightarrow> ('b list \<times> ('key \<Rightarrow> 'a)) set\<close> where
  map_fun_rel_def_internal:
    \<open>map_fun_rel D R = {(m, f). \<forall>(i, j)\<in>D. i < length m \<and> (m ! i, f j) \<in> R}\<close>

lemma map_fun_rel_def:
  \<open>\<langle>R\<rangle>map_fun_rel D = {(m, f). \<forall>(i, j)\<in>D. i < length m \<and> (m ! i, f j) \<in> R}\<close>
  unfolding relAPP_def map_fun_rel_def_internal by auto

definition map_fun_rel_assn
   :: \<open>(nat \<times> nat literal) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> (nat literal \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> assn\<close>
where
  \<open>map_fun_rel_assn D R = pure (\<langle>the_pure R\<rangle>map_fun_rel D)\<close>

lemma [safe_constraint_rules]: \<open>is_pure (map_fun_rel_assn D R)\<close>
  unfolding map_fun_rel_assn_def by auto


subsection \<open>Literals as Natural Numbers\<close>

subsubsection \<open>Definition\<close>

lemma Pos_div2_iff:
  \<open>Pos ((bb :: nat) div 2) = b \<longleftrightarrow> is_pos b \<and> (bb = 2 * atm_of b \<or> bb = 2 * atm_of b + 1)\<close>
  by (cases b) auto
lemma Neg_div2_iff:
  \<open>Neg ((bb :: nat) div 2) = b \<longleftrightarrow> is_neg b \<and> (bb = 2 * atm_of b \<or> bb = 2 * atm_of b + 1)\<close>
  by (cases b) auto

text \<open>
  Modeling \<^typ>\<open>nat literal\<close> via the transformation associating \<^term>\<open>2*n\<close> or \<^term>\<open>2*n+1\<close>
  has some advantages over the transformation to positive or negative integers: 0 is not an issue.\<close>
fun nat_of_lit :: \<open>nat literal \<Rightarrow> nat\<close> where
  \<open>nat_of_lit (Pos L) = 2*L\<close>
| \<open>nat_of_lit (Neg L) = 2*L + 1\<close>

lemma nat_of_lit_def: \<open>nat_of_lit L = (if is_pos L then 2 * atm_of L else 2 * atm_of L + 1)\<close>
  by (cases L) auto

fun literal_of_nat :: \<open>nat \<Rightarrow> nat literal\<close> where
  \<open>literal_of_nat n = (if even n then Pos (n div 2) else Neg (n div 2))\<close>

lemma lit_of_nat_nat_of_lit[simp]: \<open>literal_of_nat (nat_of_lit L) = L\<close>
  by (cases L) auto

lemma nat_of_lit_lit_of_nat[simp]: \<open>nat_of_lit (literal_of_nat n) = n\<close>
  by auto

lemma atm_of_lit_of_nat: \<open>atm_of (literal_of_nat n) = n div 2\<close>
  by auto

text \<open>There is probably a more ``closed'' form from the following theorem, but it is unclear if
  that is useful or not.\<close>
lemma uminus_lit_of_nat:
  \<open>- (literal_of_nat n) = (if even n then literal_of_nat (n+1) else literal_of_nat (n-1))\<close>
  by (auto elim!: oddE)

lemma literal_of_nat_literal_of_nat_eq[iff]: \<open>literal_of_nat x = literal_of_nat xa \<longleftrightarrow> x = xa\<close>
  by auto presburger+

definition nat_lit_rel :: \<open>(nat \<times> nat literal) set\<close> where
  \<open>nat_lit_rel =  br literal_of_nat (\<lambda>_. True)\<close>

abbreviation nat_lit_assn :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> assn\<close> where
  \<open>nat_lit_assn \<equiv> pure nat_lit_rel\<close>

definition unat_lit_rel :: \<open>(uint32 \<times> nat literal) set\<close> where
  \<open>unat_lit_rel \<equiv> uint32_nat_rel O nat_lit_rel\<close>

abbreviation unat_lit_assn :: \<open>nat literal \<Rightarrow> uint32 \<Rightarrow> assn\<close> where
  \<open>unat_lit_assn \<equiv> pure unat_lit_rel\<close>

lemma hr_comp_uint32_nat_assn_nat_lit_rel[simp]:
  \<open>hr_comp uint32_nat_assn nat_lit_rel = unat_lit_assn\<close>
  by (auto simp: hrp_comp_def hr_comp_def uint32_nat_rel_def
        hr_comp_pure br_def unat_lit_rel_def)

fun pair_of_ann_lit :: \<open>('a, 'b) ann_lit \<Rightarrow> 'a literal \<times> 'b option\<close> where
  \<open>pair_of_ann_lit (Propagated L D) = (L, Some D)\<close>
| \<open>pair_of_ann_lit (Decided L) = (L, None)\<close>

fun ann_lit_of_pair :: \<open>'a literal \<times> 'b option \<Rightarrow> ('a, 'b) ann_lit\<close> where
  \<open>ann_lit_of_pair (L, Some D) = Propagated L D\<close>
| \<open>ann_lit_of_pair (L, None) = Decided L\<close>

lemma ann_lit_of_pair_alt_def:
  \<open>ann_lit_of_pair (L, D) = (if D = None then Decided L else Propagated L (the D))\<close>
  by (cases D) auto

lemma ann_lit_of_pair_pair_of_ann_lit: \<open>ann_lit_of_pair (pair_of_ann_lit L) = L\<close>
  by (cases L) auto

lemma pair_of_ann_lit_ann_lit_of_pair: \<open>pair_of_ann_lit (ann_lit_of_pair L) = L\<close>
  by (cases L; cases \<open>snd L\<close>) auto

lemma literal_of_neq_eq_nat_of_lit_eq_iff: \<open>literal_of_nat b = L \<longleftrightarrow> b = nat_of_lit L\<close>
  by (auto simp del: literal_of_nat.simps)

lemma nat_of_lit_eq_iff[iff]: \<open>nat_of_lit xa = nat_of_lit x \<longleftrightarrow> x = xa\<close>
  apply (cases x; cases xa) by auto presburger+

lemma
   nat_lit_rel_right_unique: \<open>IS_RIGHT_UNIQUE nat_lit_rel\<close> and
   nat_lit_rel_left_unique: \<open>IS_LEFT_UNIQUE nat_lit_rel\<close>
  unfolding single_valued_def nat_lit_rel_def IS_LEFT_UNIQUE_def
  by (auto simp: br_def) presburger

definition ann_lit_rel:: \<open>('a \<times> nat) set \<Rightarrow> ('b \<times> nat option) set \<Rightarrow>
    (('a \<times> 'b) \<times> (nat, nat) ann_lit) set\<close> where
  ann_lit_rel_internal_def:
  \<open>ann_lit_rel R R' = {(a, b). \<exists>c d. (fst a, c) \<in> R \<and> (snd a, d) \<in> R' \<and>
      b = ann_lit_of_pair (literal_of_nat c, d)}\<close>

type_synonym ann_lit_wl = \<open>uint32 \<times> nat option\<close>
type_synonym ann_lits_wl = \<open>ann_lit_wl list\<close>
type_synonym ann_lit_wl_fast = \<open>uint32 \<times> uint64 option\<close>
type_synonym ann_lits_wl_fast = \<open>ann_lit_wl_fast list\<close>

definition nat_ann_lit_rel :: \<open>(ann_lit_wl \<times> (nat, nat) ann_lit) set\<close> where
  nat_ann_lit_rel_internal_def: \<open>nat_ann_lit_rel = \<langle>uint32_nat_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>ann_lit_rel\<close>

lemma ann_lit_rel_def:
  \<open>\<langle>R, R'\<rangle>ann_lit_rel = {(a, b). \<exists>c d. (fst a, c) \<in> R \<and> (snd a, d) \<in> R' \<and>
      b = ann_lit_of_pair (literal_of_nat c, d)}\<close>
  unfolding nat_ann_lit_rel_internal_def ann_lit_rel_internal_def relAPP_def ..

lemma nat_ann_lit_rel_def:
  \<open>nat_ann_lit_rel = {(a, b). b = ann_lit_of_pair ((\<lambda>(a,b). (literal_of_nat (nat_of_uint32 a), b)) a)}\<close>
  unfolding nat_ann_lit_rel_internal_def ann_lit_rel_def
  apply (auto simp: option_rel_def ex_disj_distrib uint32_nat_rel_def br_def)
   apply (case_tac b)
    apply auto
   apply (case_tac b)
   apply auto
  done

definition nat_ann_lits_rel :: \<open>(ann_lits_wl \<times> (nat, nat) ann_lits) set\<close> where
  \<open>nat_ann_lits_rel = \<langle>nat_ann_lit_rel\<rangle>list_rel\<close>

abbreviation pair_nat_ann_lit_assn :: \<open>(nat, nat) ann_lit \<Rightarrow> ann_lit_wl \<Rightarrow> assn\<close> where
  \<open>pair_nat_ann_lit_assn \<equiv> pure nat_ann_lit_rel\<close>

abbreviation pair_nat_ann_lits_assn :: \<open>(nat, nat) ann_lits \<Rightarrow> ann_lits_wl \<Rightarrow> assn\<close> where
  \<open>pair_nat_ann_lits_assn \<equiv> list_assn pair_nat_ann_lit_assn\<close>

abbreviation pair_nat_ann_lit_fast_assn :: \<open>(nat, nat) ann_lit \<Rightarrow> ann_lit_wl_fast \<Rightarrow> assn\<close> where
  \<open>pair_nat_ann_lit_fast_assn \<equiv> hr_comp (uint32_assn *a option_assn uint64_nat_assn) nat_ann_lit_rel\<close>

abbreviation pair_nat_ann_lits_fast_assn :: \<open>(nat, nat) ann_lits \<Rightarrow> ann_lits_wl_fast \<Rightarrow> assn\<close> where
  \<open>pair_nat_ann_lits_fast_assn \<equiv> list_assn pair_nat_ann_lit_fast_assn\<close>

lemma nat_ann_lits_rel_Cons[iff]:
  \<open>(x # xs, y # ys) \<in> nat_ann_lits_rel \<longleftrightarrow> (x, y) \<in> nat_ann_lit_rel \<and> (xs, ys) \<in> nat_ann_lits_rel\<close>
  by (auto simp: nat_ann_lits_rel_def)



subsubsection \<open>Code\<close>

lemma [sepref_fr_rules]: \<open>(return o id, RETURN o nat_of_lit) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: uint32_nat_rel_def br_def unat_lit_rel_def nat_lit_rel_def)

definition (in -)the_is_empty where
  \<open>the_is_empty D = Multiset.is_empty (the D)\<close>


subsection \<open>Atoms with bound\<close>

abbreviation uint_max :: nat where
  \<open>uint_max \<equiv> uint32_max\<close>

lemmas uint_max_def = uint32_max_def

context
  fixes \<A>\<^sub>i\<^sub>n :: \<open>nat multiset\<close>
begin

abbreviation D\<^sub>0 :: \<open>(nat \<times> nat literal) set\<close> where
  \<open>D\<^sub>0 \<equiv> (\<lambda>L. (nat_of_lit L, L)) ` set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)\<close>

definition length_ll_f where
  \<open>length_ll_f W L = length (W L)\<close>

lemma length_ll_length_ll_f:
  \<open>(uncurry (RETURN oo length_ll), uncurry (RETURN oo length_ll_f)) \<in>
     [\<lambda>(W, L). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0) \<times>\<^sub>r nat_lit_rel) \<rightarrow>
       \<langle>nat_rel\<rangle> nres_rel\<close>
  unfolding length_ll_def length_ll_f_def
  by (fastforce simp: fref_def map_fun_rel_def prod_rel_def nres_rel_def p2rel_def br_def
      nat_lit_rel_def)

lemma ex_list_watched:
  fixes W :: \<open>nat literal \<Rightarrow> 'a list\<close>
  shows \<open>\<exists>aa. \<forall>x\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n. nat_of_lit x < length aa \<and> aa ! nat_of_lit x = W x\<close>
  (is \<open>\<exists>aa. ?P aa\<close>)
proof -
  define D' where \<open>D' = D\<^sub>0\<close>
  define \<L>\<^sub>a\<^sub>l\<^sub>l' where \<open>\<L>\<^sub>a\<^sub>l\<^sub>l' = \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  define D'' where \<open>D'' = mset_set (snd ` D')\<close>
  let ?f = \<open>(\<lambda>L a. a[nat_of_lit L:= W L])\<close>
  interpret comp_fun_commute ?f
    apply standard
    apply (case_tac \<open>y = x\<close>)
     apply (solves simp)
    apply (intro ext)
    apply (subst (asm) lit_of_nat_nat_of_lit[symmetric])
    apply (subst (asm)(3) lit_of_nat_nat_of_lit[symmetric])
    apply (clarsimp simp only: comp_def intro!: list_update_swap)
    done
  define aa where
    \<open>aa \<equiv> fold_mset ?f (replicate (1+Max (nat_of_lit ` snd ` D')) []) (mset_set (snd ` D'))\<close>
  have length_fold: \<open>length (fold_mset (\<lambda>L a. a[nat_of_lit L := W L]) l M) = length l\<close> for l M
    by (induction M) auto
  have length_aa: \<open>length aa = Suc (Max (nat_of_lit ` snd ` D'))\<close>
    unfolding aa_def D''_def[symmetric] by (simp add: length_fold)
  have H: \<open>x \<in># \<L>\<^sub>a\<^sub>l\<^sub>l' \<Longrightarrow>
      length l \<ge> Suc (Max (nat_of_lit ` set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l'))) \<Longrightarrow>
      fold_mset (\<lambda>L a. a[nat_of_lit L := W L]) l (remdups_mset (\<L>\<^sub>a\<^sub>l\<^sub>l')) ! nat_of_lit x = W x\<close>
    for x l \<L>\<^sub>a\<^sub>l\<^sub>l'
    unfolding \<L>\<^sub>a\<^sub>l\<^sub>l'_def[symmetric]
    apply (induction \<L>\<^sub>a\<^sub>l\<^sub>l' arbitrary: l)
    subgoal by simp
    subgoal for xa Ls l
      apply (case_tac \<open>(nat_of_lit ` set_mset Ls) = {}\<close>)
       apply (solves simp)
      apply (auto simp: less_Suc_eq_le length_fold)
      done
    done
  have H': \<open>aa ! nat_of_lit x = W x\<close> if \<open>x \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n\<close> for x
    using that unfolding aa_def D'_def
    by (auto simp: D'_def image_image remdups_mset_def[symmetric]
        less_Suc_eq_le intro!: H)
  have \<open>?P aa\<close>
    by (auto simp: D'_def image_image remdups_mset_def[symmetric]
        less_Suc_eq_le length_aa H')
  then show ?thesis
    by blast
qed

definition isasat_input_bounded where
  [simp]: \<open>isasat_input_bounded = (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n. nat_of_lit L \<le> uint_max)\<close>

definition isasat_input_nempty where
  [simp]: \<open>isasat_input_nempty = (set_mset \<A>\<^sub>i\<^sub>n \<noteq> {})\<close>

definition isasat_input_bounded_nempty where
  \<open>isasat_input_bounded_nempty = (isasat_input_bounded \<and> isasat_input_nempty)\<close>

context
  assumes in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max: \<open>isasat_input_bounded\<close>
begin

lemma in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max': \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n \<Longrightarrow> nat_of_lit L \<le> uint_max\<close>
  using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max by auto

lemma in_\<A>\<^sub>i\<^sub>n_less_than_uint_max_div_2:
  \<open>L \<in># \<A>\<^sub>i\<^sub>n \<Longrightarrow> L \<le> uint_max div 2\<close>
  using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max'[of \<open>Neg L\<close>]
  unfolding Ball_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
  by (auto simp: uint_max_def)

lemma simple_clss_size_upper_div2':
  assumes
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n  \<A>\<^sub>i\<^sub>n C\<close> and
    dist: \<open>distinct_mset C\<close> and
    tauto: \<open>\<not>tautology C\<close> and
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max: \<open>\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n. nat_of_lit L < uint_max - 1\<close>
  shows \<open>size C \<le> uint_max div 2\<close>
proof -
  let ?C = \<open>atm_of `# C\<close>
  have \<open>distinct_mset ?C\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then obtain K where \<open>\<not>count (atm_of `# C) K \<le> Suc 0\<close>
      unfolding distinct_mset_count_less_1
      by auto
    then have \<open>count (atm_of `# C) K \<ge> 2\<close>
      by auto
    then obtain L L' C' where
      C: \<open>C = {#L, L'#} + C'\<close> and L_L': \<open>atm_of L = atm_of L'\<close>
      by (auto dest!: count_image_mset_multi_member_split_2)
    then show False
      using dist tauto by (auto simp: atm_of_eq_atm_of tautology_add_mset)
  qed
  then have card: \<open>size ?C = card (set_mset ?C)\<close>
    using distinct_mset_size_eq_card by blast
  have size: \<open>size ?C = size C\<close>
    using dist tauto
    by (induction C) (auto simp: tautology_add_mset)
  have m: \<open>set_mset ?C \<subseteq> {0..<uint_max div 2}\<close>
  proof
    fix L
    assume \<open>L \<in> set_mset ?C\<close>
    then have \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)\<close>
    using lits by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def atm_of_lit_in_atms_of
        in_all_lits_of_m_ain_atms_of_iff subset_iff)
    then have \<open>Pos L \<in># (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)\<close>
      using lits by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    then have \<open>nat_of_lit (Pos L) < uint_max - 1\<close>
      using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max by (auto simp: atm_of_lit_in_atms_of
        in_all_lits_of_m_ain_atms_of_iff subset_iff)
    then have \<open>L < uint_max div 2\<close>
       by (auto simp: atm_of_lit_in_atms_of
        in_all_lits_of_m_ain_atms_of_iff subset_iff uint_max_def)
    then show \<open>L \<in> {0..<uint_max div 2}\<close>
       by (auto simp: atm_of_lit_in_atms_of uint_max_def
        in_all_lits_of_m_ain_atms_of_iff subset_iff)
  qed
  moreover have \<open>card \<dots> =  uint_max div 2\<close>
    by auto
  ultimately have \<open>card (set_mset ?C) \<le> uint_max div 2\<close>
    using card_mono[OF _ m] by auto
  then show ?thesis
    unfolding card[symmetric] size .
qed


lemma simple_clss_size_upper_div2:
  assumes
   lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n  \<A>\<^sub>i\<^sub>n C\<close> and
   dist: \<open>distinct_mset C\<close> and
   tauto: \<open>\<not>tautology C\<close>
  shows \<open>size C \<le> 1 + uint_max div 2\<close>
proof -
  let ?C = \<open>atm_of `# C\<close>
  have \<open>distinct_mset ?C\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then obtain K where \<open>\<not>count (atm_of `# C) K \<le> Suc 0\<close>
      unfolding distinct_mset_count_less_1
      by auto
    then have \<open>count (atm_of `# C) K \<ge> 2\<close>
      by auto
    then obtain L L' C' where
      C: \<open>C = {#L, L'#} + C'\<close> and L_L': \<open>atm_of L = atm_of L'\<close>
      by (auto dest!: count_image_mset_multi_member_split_2)
    then show False
      using dist tauto by (auto simp: atm_of_eq_atm_of tautology_add_mset)
  qed
  then have card: \<open>size ?C = card (set_mset ?C)\<close>
    using distinct_mset_size_eq_card by blast
  have size: \<open>size ?C = size C\<close>
    using dist tauto
    by (induction C) (auto simp: tautology_add_mset)
  have m: \<open>set_mset ?C \<subseteq> {0..uint_max div 2}\<close>
  proof
    fix L
    assume \<open>L \<in> set_mset ?C\<close>
    then have \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l  \<A>\<^sub>i\<^sub>n)\<close>
    using lits by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def atm_of_lit_in_atms_of
        in_all_lits_of_m_ain_atms_of_iff subset_iff)
    then have \<open>Pos L \<in># (\<L>\<^sub>a\<^sub>l\<^sub>l  \<A>\<^sub>i\<^sub>n)\<close>
      using lits by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    then have \<open>nat_of_lit (Pos L) \<le> uint_max\<close>
      using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max by (auto simp: atm_of_lit_in_atms_of
        in_all_lits_of_m_ain_atms_of_iff subset_iff)
    then have \<open>L \<le> uint_max div 2\<close>
       by (auto simp: atm_of_lit_in_atms_of
        in_all_lits_of_m_ain_atms_of_iff subset_iff uint_max_def)
    then show \<open>L \<in> {0 .. uint_max div 2}\<close>
       by (auto simp: atm_of_lit_in_atms_of uint_max_def
        in_all_lits_of_m_ain_atms_of_iff subset_iff)
  qed
  moreover have \<open>card \<dots> =  1 + uint_max div 2\<close>
    by auto
  ultimately have \<open>card (set_mset ?C) \<le> 1 + uint_max div 2\<close>
    using card_mono[OF _ m] by auto
  then show ?thesis
    unfolding card[symmetric] size .
qed

lemma clss_size_uint_max:
  assumes
   lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n C\<close> and
   dist: \<open>distinct_mset C\<close>
  shows \<open>size C \<le> uint_max + 2\<close>
proof -
  let ?posC = \<open>filter_mset is_pos C\<close>
  let ?negC = \<open>filter_mset is_neg C\<close>
  have C: \<open>C = ?posC + ?negC\<close>
    apply (subst multiset_partition[of _ is_pos])
    by auto
  have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n ?posC\<close>
    by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF lits]) auto
  moreover have \<open>distinct_mset ?posC\<close>
    by (rule distinct_mset_mono[OF _dist]) auto
  ultimately have pos: \<open>size ?posC \<le> 1 + uint_max div 2\<close>
    by (rule simple_clss_size_upper_div2) (auto simp: tautology_decomp)

  have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n ?negC\<close>
    by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF lits]) auto
  moreover have \<open>distinct_mset ?negC\<close>
    by (rule distinct_mset_mono[OF _dist]) auto
  ultimately have neg: \<open>size ?negC \<le> 1 + uint_max div 2\<close>
    by (rule simple_clss_size_upper_div2) (auto simp: tautology_decomp)

  show ?thesis
    apply (subst C)
    apply (subst size_union)
    using pos neg by linarith
qed

lemma clss_size_uint64_max:
  assumes
   lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n C\<close> and
   dist: \<open>distinct_mset C\<close>
 shows \<open>size C < uint64_max\<close>
  using clss_size_uint_max[OF assms] by (auto simp: uint32_max_def uint64_max_def)

lemma clss_size_upper:
  assumes
   lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n C\<close> and
   dist: \<open>distinct_mset C\<close> and
   in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max: \<open>\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n. nat_of_lit L < uint_max - 1\<close>
 shows \<open>size C \<le> uint_max\<close>
proof -
  let ?A = \<open>remdups_mset (atm_of `# C)\<close>
  have [simp]: \<open>distinct_mset (poss ?A)\<close> \<open>distinct_mset (negs ?A)\<close>
    by (simp_all add: distinct_image_mset_inj inj_on_def)

  have \<open>C \<subseteq># poss ?A + negs ?A\<close>
    apply (rule distinct_subseteq_iff[THEN iffD1])
    subgoal by (auto simp: dist distinct_mset_add disjunct_not_in)
    subgoal by (auto simp: dist distinct_mset_add disjunct_not_in)
    subgoal
      apply rule
      using literal.exhaust_sel by (auto simp: image_iff)
    done
  have [simp]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n (poss ?A)\<close> \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n (negs ?A)\<close>
    using lits
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_negs_remdups_mset literals_are_in_\<L>\<^sub>i\<^sub>n_poss_remdups_mset)

  have \<open>\<not> tautology (poss ?A)\<close> \<open>\<not> tautology (negs ?A)\<close>
    by (auto simp: tautology_decomp)
  then have \<open>size (poss ?A) \<le> uint_max div 2\<close> and \<open>size (negs ?A) \<le> uint_max div 2\<close>
    using simple_clss_size_upper_div2'[of \<open>poss ?A\<close>]
      simple_clss_size_upper_div2'[of \<open>negs ?A\<close>] in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max
    by auto
  then have \<open>size C \<le> uint_max div 2 + uint_max div 2\<close>
    using \<open>C \<subseteq># poss (remdups_mset (atm_of `# C)) + negs (remdups_mset (atm_of `# C))\<close>
      size_mset_mono by fastforce
  then show ?thesis by (auto simp: uint_max_def)
qed

lemma
  assumes
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A>\<^sub>i\<^sub>n M\<close> and
    n_d: \<open>no_dup M\<close>
  shows
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_length_le_uint32_max:
      \<open>length M \<le> Suc (uint_max div 2)\<close> and
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_count_decided_uint_max:
      \<open>count_decided M \<le> Suc (uint_max div 2)\<close> and
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max:
      \<open>get_level M L \<le> Suc (uint_max div 2)\<close>
proof -
  have \<open>length M = card (atm_of ` lits_of_l M)\<close>
    using no_dup_length_eq_card_atm_of_lits_of_l[OF n_d] .
  moreover have \<open>atm_of ` lits_of_l M \<subseteq> set_mset \<A>\<^sub>i\<^sub>n\<close>
    using lits unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_trail_atm_of by auto
  ultimately have \<open>length M \<le> card (set_mset \<A>\<^sub>i\<^sub>n)\<close>
    by (simp add: card_mono)
  moreover {
    have \<open>set_mset \<A>\<^sub>i\<^sub>n \<subseteq> {0 ..< (uint_max div 2) + 1}\<close>
      using in_\<A>\<^sub>i\<^sub>n_less_than_uint_max_div_2 by (fastforce simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
          Ball_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n uint_max_def)
    from subset_eq_atLeast0_lessThan_card[OF this] have \<open>card (set_mset \<A>\<^sub>i\<^sub>n) \<le> uint_max div 2 + 1\<close>
      .
  }
  ultimately show \<open>length M \<le> Suc (uint_max div 2)\<close>
    by linarith
  moreover have \<open>count_decided M \<le> length M\<close>
    unfolding count_decided_def by auto
  ultimately show \<open>count_decided M \<le> Suc (uint_max div 2)\<close> by simp
  then show \<open>get_level M L \<le> Suc (uint_max div 2)\<close>
    using count_decided_ge_get_level[of M L]
    by simp
qed

lemma length_trail_uint_max_div2:
  fixes M :: \<open>(nat, 'b) ann_lits\<close>
  assumes
    M_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n\<close> and
    n_d: \<open>no_dup M\<close>
  shows \<open>length M \<le> uint_max div 2 + 1\<close>
proof -
  have dist_atm_M: \<open>distinct_mset {#atm_of (lit_of x). x \<in># mset M#}\<close>
    using n_d by (metis distinct_mset_mset_distinct mset_map no_dup_def)
  have incl: \<open>atm_of `# lit_of `# mset M \<subseteq># remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using assms dist_atm_M
    by (auto 5 5 simp: Decided_Propagated_in_iff_in_lits_of_l lits_of_def no_dup_distinct
        atm_of_eq_atm_of)
  have inj_on: \<open>inj_on nat_of_lit (set_mset (remdups_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)))\<close>
    by (auto simp: inj_on_def)
  have H: \<open>xa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n \<Longrightarrow> atm_of xa \<le> uint_max div 2\<close> for xa
    using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max
    by (cases xa) (auto simp: uint_max_def)
  have \<open>remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n) \<subseteq># mset [0..< 1 + (uint_max div 2)]\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using H distinct_image_mset_inj[OF inj_on]
    by (force simp del: literal_of_nat.simps simp: distinct_mset_mset_set
        dest: le_neq_implies_less)+
  note _ = size_mset_mono[OF this]
  moreover have \<open>size (nat_of_lit `# remdups_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)) = size (remdups_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n))\<close>
    by simp
  ultimately have 2: \<open>size (remdups_mset (atm_of `# (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n))) \<le> 1 + uint_max div 2\<close>
    by auto
  from size_mset_mono[OF incl] have 1: \<open>length M \<le> size (remdups_mset (atm_of `# (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)))\<close>
    unfolding uint_max_def count_decided_def
    by (auto simp del: length_filter_le)
  with 2 show ?thesis
    by (auto simp: uint32_max_def)
qed

end

end

text \<open>
  First we instantiate our types with sort heap and default, to have compatibility with code
  generation. The idea is simplify to create injections into the components of our datatypes.
\<close>
instance literal :: (heap) heap
proof standard
  obtain f :: \<open>'a \<Rightarrow> nat\<close> where f: \<open>inj f\<close>
    by blast
  then have Hf: \<open>f x = f s \<longleftrightarrow> x = s\<close> for s x
    unfolding inj_on_def Ball_def comp_def by blast
  let ?f = \<open>\<lambda>L. (is_pos L, f (atm_of L))\<close>
  have \<open>OFCLASS(bool \<times> nat, heap_class)\<close>
   by standard
  then obtain g :: \<open>bool \<times> nat \<Rightarrow> nat\<close> where g: \<open>inj g\<close>
    by blast
  then have H: \<open>g (x, y) = g (s, t) \<longleftrightarrow> x = s \<and> y = t\<close> for s t x y
    unfolding inj_on_def Ball_def comp_def by blast
  have \<open>inj (g o ?f)\<close>
    using f g unfolding inj_on_def Ball_def comp_def H Hf
    apply (intro allI impI)
    apply (rename_tac x y, case_tac x; case_tac y)
    by auto
  then show \<open>\<exists>to_nat:: 'a literal \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instance annotated_lit :: (heap, heap, heap) heap
proof standard
  let ?f = \<open>\<lambda>L:: ('a, 'b, 'c) annotated_lit.
      (if is_decided L then Some (lit_dec L) else None,
       if is_decided L then None else Some (lit_prop L), if is_decided L then None else Some (mark_of L))\<close>
  have f: \<open>inj ?f\<close>
    unfolding inj_on_def Ball_def
    apply (intro allI impI)
    apply (rename_tac x y, case_tac x; case_tac y)
    by auto
  then have Hf: \<open>?f x = ?f s \<longleftrightarrow> x = s\<close> for s x
    unfolding inj_on_def Ball_def comp_def by blast
  have \<open>OFCLASS('a option \<times> 'b option \<times> 'c option, heap_class)\<close>
   by standard
  then obtain g :: \<open>'a option \<times> 'b option \<times> 'c option \<Rightarrow> nat\<close> where g: \<open>inj g\<close>
    by blast
  then have H: \<open>g (x, y) = g (s, t) \<longleftrightarrow> x = s \<and> y = t\<close> for s t x y
    unfolding inj_on_def Ball_def comp_def by blast
  have \<open>inj (g o ?f)\<close>
    using f g unfolding inj_on_def Ball_def comp_def H Hf
    apply (intro allI impI)
    apply (rename_tac x y, case_tac x; case_tac y)
    by auto
  then show \<open>\<exists>to_nat:: ('a, 'b, 'c) annotated_lit \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation literal :: (default) default
begin

definition default_literal where
\<open>default_literal = Pos default\<close>
instance by standard

end

instantiation fmap :: (type, type) default
begin

definition default_fmap where
\<open>default_fmap = fmempty\<close>
instance by standard

end


subsection \<open>Declaration of some Operators and Implementation\<close>

sepref_decl_op atm_of: \<open>atm_of :: nat literal \<Rightarrow> nat\<close> ::
  \<open>(Id :: (nat literal \<times> _) set) \<rightarrow> (Id :: (nat \<times> _) set)\<close> .

lemma [def_pat_rules]:
  \<open>atm_of \<equiv> op_atm_of\<close>
  by auto

sepref_decl_op lit_of: \<open>lit_of :: (nat, nat) ann_lit \<Rightarrow> nat literal\<close> ::
  \<open>(Id :: ((nat, nat) ann_lit \<times> _) set) \<rightarrow> (Id :: (nat literal \<times> _) set)\<close> .

lemma [def_pat_rules]:
  \<open>lit_of \<equiv> op_lit_of\<close>
  by auto


lemma \<open>(return o (\<lambda>n. shiftr n 1), RETURN o shiftr1) \<in> word_nat_assn\<^sup>k \<rightarrow>\<^sub>a word_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: shiftr1_def word_nat_rel_def unat_shiftr br_def)

section \<open>Code Generation\<close>

subsection \<open>Literals as Natural Numbers\<close>

definition propagated where
  \<open>propagated L C = (L, Some C)\<close>

lemma propagated_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo propagated), uncurry (RETURN oo Propagated)) \<in>
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a pair_nat_ann_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: nat_ann_lit_rel_def propagated_def case_prod_beta p2rel_def
      br_def uint32_nat_rel_def unat_lit_rel_def nat_lit_rel_def
      split: option.splits)

definition decided where
  \<open>decided L = (L, None)\<close>

lemma decided_hnr[sepref_fr_rules]:
  \<open>(return o decided, RETURN o Decided) \<in>
     unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a pair_nat_ann_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: nat_ann_lit_rel_def decided_def case_prod_beta p2rel_def
      br_def uint32_nat_rel_def unat_lit_rel_def nat_lit_rel_def
      split: option.splits)

definition uminus_lit_imp :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>uminus_lit_imp L = bitXOR L 1\<close>

lemma uminus_lit_imp_uminus:
  \<open>(RETURN o uminus_lit_imp, RETURN o uminus) \<in>
     nat_lit_rel \<rightarrow>\<^sub>f \<langle>nat_lit_rel\<rangle>nres_rel\<close>
  unfolding bitXOR_1_if_mod_2 uminus_lit_imp_def
  by (intro frefI nres_relI) (auto simp: nat_ann_lit_rel_def uminus_lit_imp_def case_prod_beta p2rel_def
      br_def nat_lit_rel_def split: option.splits, presburger)

definition uminus_code :: \<open>uint32 \<Rightarrow> uint32\<close> where
  \<open>uminus_code L = bitXOR L 1\<close>

lemma uminus_lit_hnr[sepref_fr_rules]:
  \<open>(return o uminus_code, RETURN o uminus) \<in>
     unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
proof -
  have [simp]: \<open>nat_of_uint32 1 = 1\<close>
    by transfer auto
  have [simp]: \<open>0 XOR Suc 0 = Suc 0\<close>
    unfolding bitXOR_nat_def
    by auto
  have [simp]: \<open>bin_last (2 + n) = bin_last n\<close> for n
    by (auto simp: bin_last_def)
  have [simp]: \<open>bin_rest (2 + n) = 1 + (bin_rest n)\<close> for n
    by (auto simp: bin_rest_def)
  have \<open>bin_nth (2 + n XOR 1) na \<longleftrightarrow> bin_nth (2 + (n XOR 1)) na\<close> for n na
    by (induction na)  auto

  then have [simp]: \<open>((2 + n) XOR 1) = 2 + ( ( ( n XOR 1)))\<close> for n :: int
    by (auto simp: bin_eq_iff)

  have [simp]: \<open>Suc (Suc n) XOR Suc 0 = Suc (Suc (n XOR Suc 0))\<close> for n :: nat
    unfolding bitXOR_nat_def
    by (auto simp: nat_add_distrib)

  have [simp]: \<open>2 * q XOR Suc 0 = Suc (2 * q)\<close> for q :: nat
    by (induction q)  auto

  have 1: \<open>(return o (\<lambda>L. bitXOR L 1), RETURN o uminus_lit_imp) \<in>
     uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
    unfolding bitXOR_1_if_mod_2 uminus_lit_imp_def
    apply sepref_to_hoare
    apply (sep_auto simp: nat_ann_lit_rel_def uminus_lit_imp_def case_prod_beta p2rel_def
        uint32_nat_rel_def br_def nat_of_uint32_XOR bitXOR_1_if_mod_2
        split: option.splits)
    using One_nat_def bitXOR_1_if_mod_2 by presburger
  show ?thesis
    using 1[FCOMP uminus_lit_imp_uminus] unfolding unat_lit_rel_def uminus_code_def .
qed


subsection \<open>State Conversion\<close>

subsubsection \<open>Functions and Types:\<close>

type_synonym clauses_wl = \<open>uint32 arrayO_raa\<close>

abbreviation ann_lit_wl_assn :: \<open>ann_lit_wl \<Rightarrow> ann_lit_wl \<Rightarrow> assn\<close> where
  \<open>ann_lit_wl_assn \<equiv> uint32_assn *a (option_assn nat_assn)\<close>

abbreviation ann_lit_wl_fast_assn :: \<open>ann_lit_wl \<Rightarrow> ann_lit_wl_fast \<Rightarrow> assn\<close> where
  \<open>ann_lit_wl_fast_assn \<equiv> uint32_assn *a (option_assn uint64_nat_assn)\<close>

abbreviation ann_lits_wl_assn :: \<open>ann_lits_wl \<Rightarrow> ann_lits_wl \<Rightarrow> assn\<close> where
  \<open>ann_lits_wl_assn \<equiv> list_assn ann_lit_wl_assn\<close>

abbreviation clause_ll_assn :: \<open>nat clause_l \<Rightarrow> clause_wl \<Rightarrow> assn\<close> where
  \<open>clause_ll_assn \<equiv> array_assn unat_lit_assn\<close>

abbreviation clause_l_assn :: \<open>nat clause \<Rightarrow> uint32 list \<Rightarrow> assn\<close> where
  \<open>clause_l_assn \<equiv> list_mset_assn unat_lit_assn\<close>

abbreviation clauses_l_assn :: \<open>nat clauses \<Rightarrow> uint32 list list \<Rightarrow> assn\<close> where
  \<open>clauses_l_assn \<equiv> list_mset_assn clause_l_assn\<close>

abbreviation clauses_to_update_l_assn :: \<open>nat multiset \<Rightarrow> nat list \<Rightarrow> assn\<close> where
  \<open>clauses_to_update_l_assn \<equiv> list_mset_assn nat_assn\<close>

abbreviation clauses_to_update_ll_assn :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> assn\<close> where
  \<open>clauses_to_update_ll_assn \<equiv> list_assn nat_assn\<close>

abbreviation unit_lits_assn :: \<open>nat clauses \<Rightarrow> unit_lits_wl \<Rightarrow> assn\<close> where
  \<open>unit_lits_assn \<equiv> list_mset_assn (list_mset_assn unat_lit_assn)\<close>

type_synonym nat_clauses_l = \<open>nat list list\<close>

lemma clause_l_assn_alt_def:
  \<open>clause_l_assn = hr_comp (list_assn unat_lit_assn) list_mset_rel\<close>
  by (simp add: list_assn_list_mset_rel_eq_list_mset_assn)


subsubsection \<open>Refinement of the Watched Function\<close>

sepref_register \<open>watched_by :: nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat watched\<close>
   :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat watched\<close>

definition watched_by_nth :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close> where
  \<open>watched_by_nth = (\<lambda>(M, N, D, NE, UE, Q, W) L i. W L ! i)\<close>

definition watched_app
  :: \<open>(nat literal \<Rightarrow> (nat watcher) list) \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close> where
  \<open>watched_app M L i \<equiv> M L ! i\<close>

sepref_decl_op watched_app:
  \<open>watched_app ::(nat literal \<Rightarrow> (nat \<times> _) list) \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close>
::
  \<open>(Id :: ((nat literal \<Rightarrow> (nat watcher) list) \<times> _) set) \<rightarrow> (Id :: (nat literal \<times> _) set) \<rightarrow> nat_rel \<rightarrow>
     nat_rel \<times>\<^sub>r (Id :: (nat literal \<times> _) set) \<times>\<^sub>r bool_rel\<close>
  .

lemma [def_pat_rules]:
  \<open>watched_app $ M $ L $ i \<equiv> op_watched_app $ M $ L $ i\<close>
  by (auto simp: watched_app_def)

lemma watched_by_nth_watched_app:
  \<open>watched_by S K ! w = watched_app ((snd o snd o snd o snd o snd o snd) S) K w\<close>
  by (cases S) (auto simp: watched_app_def)


subsubsection \<open>More Operations\<close>

lemma nat_of_uint32_shiftr: \<open>nat_of_uint32 (shiftr xi n) = shiftr (nat_of_uint32 xi) n\<close>
  by transfer (auto simp: shiftr_div_2n unat_def shiftr_nat_def)

definition atm_of_code :: \<open>uint32 \<Rightarrow> uint32\<close> where
  \<open>atm_of_code L = shiftr L 1\<close>

lemma atm_of_hnr[sepref_fr_rules]:
  \<open>(return o atm_of_code, RETURN o op_atm_of) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: p2rel_def uint32_nat_rel_def br_def
      Collect_eq_comp unat_lit_rel_def nat_of_uint32_shiftr nat_lit_rel_def atm_of_code_def)

lemma lit_of_hnr[sepref_fr_rules]:
  \<open>(return o fst, RETURN o op_lit_of) \<in> pair_nat_ann_lit_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: p2rel_def nat_ann_lit_rel_def uint32_nat_rel_def
      Collect_eq_comp br_def unat_lit_rel_def nat_lit_rel_def ann_lit_of_pair_alt_def
      split: if_splits)

lemma lit_of_fast_hnr[sepref_fr_rules]:
  \<open>(return o fst, RETURN o op_lit_of) \<in> pair_nat_ann_lit_fast_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: unat_lit_rel_def uint32_nat_rel_def)
  apply (sep_auto simp: p2rel_def nat_ann_lit_rel_def uint32_nat_rel_def
      Collect_eq_comp br_def unat_lit_rel_def nat_lit_rel_def ann_lit_of_pair_alt_def
      hr_comp_def prod.splits case_prod_beta
      split: if_splits)
  done

lemma op_eq_op_nat_lit_eq[sepref_fr_rules]:
  \<open>(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in>
    (pure unat_lit_rel)\<^sup>k *\<^sub>a (pure unat_lit_rel)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have [simp]: \<open>even bi \<Longrightarrow> even ai \<Longrightarrow> ai div 2 = bi div 2 \<Longrightarrow> ai = bi\<close> for ai bi :: nat
    by presburger
  have [dest]: \<open>odd bi \<Longrightarrow> odd ai \<Longrightarrow> ai div 2 = bi div 2 \<Longrightarrow> ai = bi\<close> for ai bi :: nat
    by presburger
  show ?thesis
    by sepref_to_hoare
       (sep_auto simp: p2rel_def nat_ann_lit_rel_def nat_lit_rel_def
        br_def Collect_eq_comp uint32_nat_rel_def dvd_div_eq_iff unat_lit_rel_def
      split: if_splits)+
qed


subsection \<open>Code Generation\<close>

subsubsection \<open>More Operations\<close>

definition literals_to_update_wl_empty :: \<open>nat twl_st_wl \<Rightarrow> bool\<close>  where
  \<open>literals_to_update_wl_empty = (\<lambda>(M, N, D, NE, UE, Q, W). Q = {#})\<close>

lemma in_nat_list_rel_list_all2_in_set_iff:
    \<open>(a, aa) \<in> nat_lit_rel \<Longrightarrow>
       list_all2 (\<lambda>x x'. (x, x') \<in> nat_lit_rel) b ba \<Longrightarrow>
       a \<in> set b \<longleftrightarrow> aa \<in> set ba\<close>
  apply (subgoal_tac \<open>length b = length ba\<close>)
  subgoal
    apply (rotate_tac 2)
    apply (induction b ba rule: list_induct2)
     apply (solves simp)
    apply (auto simp: p2rel_def nat_lit_rel_def br_def, presburger)[]
    done
  subgoal using list_all2_lengthD by auto
  done

definition is_decided_wl where
  \<open>is_decided_wl L \<longleftrightarrow> snd L = None\<close>

lemma is_decided_wl_is_decided:
  \<open>(RETURN o is_decided_wl, RETURN o is_decided) \<in> nat_ann_lit_rel \<rightarrow> \<langle>bool_rel\<rangle> nres_rel\<close>
  by (auto simp: nat_ann_lit_rel_def is_decided_wl_def is_decided_def intro!: frefI nres_relI
      elim: ann_lit_of_pair.elims)

sepref_definition is_decided_wl_code
  is \<open>(RETURN o is_decided_wl)\<close>
  :: \<open>ann_lit_wl_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding is_decided_wl_def[abs_def]
  by sepref

sepref_definition is_decided_wl_fast_code
  is \<open>(RETURN o is_decided_wl)\<close>
  :: \<open>ann_lit_wl_fast_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding is_decided_wl_def[abs_def]
  by sepref

lemma ann_lit_of_pair_if:
  \<open>ann_lit_of_pair (L, D) = (if D = None then Decided L else Propagated L (the D))\<close>
  by (cases D) auto

lemma
  is_decided_wl_code[sepref_fr_rules]:
    \<open>(is_decided_wl_code, RETURN o is_decided) \<in> pair_nat_ann_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close> (is ?slow) and
  is_decided_wl_fast_code[sepref_fr_rules]:
    \<open>(is_decided_wl_fast_code, RETURN o is_decided) \<in> pair_nat_ann_lit_fast_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
   (is ?fast)
proof -
  have 1: \<open>hr_comp ann_lit_wl_assn nat_ann_lit_rel = pair_nat_ann_lit_assn\<close>
    by (fastforce simp: case_prod_beta hr_comp_def[abs_def] pure_def nat_ann_lit_rel_def
        prod_assn_def ann_lit_of_pair_if ex_assn_def imp_ex Abs_assn_eqI(1) ex_simps(1)[symmetric]
        simp del: pair_of_ann_lit.simps literal_of_nat.simps ex_simps(1)
        split: if_splits)
  show ?slow
    using is_decided_wl_code.refine[FCOMP is_decided_wl_is_decided]
    unfolding 1 .
  show ?fast
    using is_decided_wl_fast_code.refine[FCOMP is_decided_wl_is_decided]
    unfolding 1 .
qed

definition get_maximum_level_remove where
  \<open>get_maximum_level_remove M D L =  get_maximum_level M (remove1_mset L D)\<close>

lemma in_list_all2_ex_in: \<open>a \<in> set xs \<Longrightarrow> list_all2 R xs ys \<Longrightarrow> \<exists>b \<in> set ys. R a b\<close>
  apply (subgoal_tac \<open>length xs = length ys\<close>)
   apply (rotate_tac 2)
   apply (induction xs ys rule: list_induct2)
    apply ((solves auto)+)[2]
  using list_all2_lengthD by blast

lemma
  nat_lit_assn_right_unique:
    \<open>CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) nat_lit_assn\<close> and
  nat_lit_assn_left_unique:
    \<open>CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) nat_lit_assn\<close>
   by (auto simp: IS_PURE_def single_valued_def p2rel_def IS_LEFT_UNIQUE_def nat_lit_rel_def
      br_def, presburger)

definition find_decomp_wl_imp :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clause \<Rightarrow> nat literal \<Rightarrow> (nat, nat) ann_lits nres\<close> where
  \<open>find_decomp_wl_imp = (\<lambda>M\<^sub>0 D L. do {
    let lev = get_maximum_level M\<^sub>0 (remove1_mset (-L) D);
    let k = count_decided M\<^sub>0;
    (_, M) \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(j, M). j = count_decided M \<and> j \<ge> lev \<and>
           (M = [] \<longrightarrow> j = lev) \<and>
           (\<exists>M'. M\<^sub>0 = M' @ M \<and> (j = lev \<longrightarrow> M' \<noteq> [] \<and> is_decided (last M')))\<^esup>
         (\<lambda>(j, M). j > lev)
         (\<lambda>(j, M). do {
            ASSERT(M \<noteq> []);
            if is_decided (hd M)
            then RETURN (j-1, tl M)
            else RETURN (j, tl M)}
         )
         (k, M\<^sub>0);
    RETURN M
  })\<close>

lemma ex_decomp_get_ann_decomposition_iff:
  \<open>(\<exists>M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)) \<longleftrightarrow>
    (\<exists>M2. M = M2 @ Decided K # M1)\<close>
  using get_all_ann_decomposition_ex by fastforce

lemma count_decided_tl_if:
  \<open>M \<noteq> [] \<Longrightarrow> count_decided (tl M) = (if is_decided (hd M) then count_decided M - 1 else count_decided M)\<close>
  by (cases M) auto

lemma count_decided_butlast:
  \<open>count_decided (butlast xs) = (if is_decided (last xs) then count_decided xs - 1 else count_decided xs)\<close>
  by (cases xs rule: rev_cases) (auto simp: count_decided_def)

definition find_decomp_wl' where
  \<open>find_decomp_wl' =
     (\<lambda>(M::(nat, nat) ann_lits) (D::nat clause) (L::nat literal).
        SPEC(\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (D - {#-L#}) + 1))\<close>

definition get_conflict_wl_is_None :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None = (\<lambda>(M, N, D, NE, UE, Q, W). is_None D)\<close>

lemma get_conflict_wl_is_None: \<open>get_conflict_wl S = None \<longleftrightarrow> get_conflict_wl_is_None S\<close>
  by (cases S) (auto simp: get_conflict_wl_is_None_def split: option.splits)

lemma watched_by_nth_watched_app':
  \<open>watched_by S K = ((snd o snd o snd o snd o snd o snd) S) K\<close>
  by (cases S) (auto simp: watched_app_def)


lemma (in -) safe_minus_nat_assn:
  \<open>(uncurry (return oo (-)), uncurry (RETURN oo fast_minus)) \<in>
     [\<lambda>(m, n). m \<ge> n]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_le_minus
      nat_of_uint32_notle_minus nat_of_uint32_le_iff)

lemma (in -) hd_decided_count_decided_ge_1:
  \<open>x \<noteq> [] \<Longrightarrow> is_decided (hd x) \<Longrightarrow> Suc 0 \<le> count_decided x\<close>
  by (cases x) auto

definition (in -) find_decomp_wl_imp' :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clause_l list \<Rightarrow> nat \<Rightarrow>
    nat clause \<Rightarrow> nat clauses \<Rightarrow> nat clauses \<Rightarrow> nat lit_queue_wl \<Rightarrow>
    (nat literal \<Rightarrow> nat watched) \<Rightarrow> _ \<Rightarrow> (nat, nat) ann_lits nres\<close> where
  \<open>find_decomp_wl_imp' = (\<lambda>M N U D NE UE W Q L. find_decomp_wl_imp M D L)\<close>

lemma nth_ll_watched_app:
  \<open>(uncurry2 (RETURN ooo nth_rll), uncurry2 (RETURN ooo watched_app)) \<in>
     [\<lambda>((W, L), i). L \<in># (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)) \<times>\<^sub>r nat_lit_rel) \<times>\<^sub>r nat_rel \<rightarrow>
       \<langle>nat_rel \<times>\<^sub>r Id\<rangle> nres_rel\<close>
  unfolding watched_app_def nth_rll_def
  by (fastforce simp: fref_def map_fun_rel_def prod_rel_def nres_rel_def p2rel_def br_def
      nat_lit_rel_def)

lemma ex_literal_of_nat: \<open>\<exists>bb. b = literal_of_nat bb\<close>
  by (cases b)
    (auto simp: nat_of_lit_def split: if_splits; presburger; fail)+


definition (in -) is_pos_code :: \<open>uint32 \<Rightarrow> bool\<close> where
  \<open>is_pos_code L \<longleftrightarrow> bitAND L 1 = 0\<close>

lemma (in -) is_pos_hnr[sepref_fr_rules]:
  \<open>(return o is_pos_code, RETURN o is_pos) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have 1: \<open>(RETURN o (\<lambda>L. bitAND L 1 = 0), RETURN o is_pos) \<in> nat_lit_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
    unfolding bitAND_1_mod_2 is_pos_code_def
    by (intro nres_relI frefI) (auto simp: nat_lit_rel_def br_def split: if_splits, presburger)
  have 2: \<open>(return o is_pos_code, RETURN o (\<lambda>L. bitAND L 1 = 0)) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    apply sepref_to_hoare
    using nat_of_uint32_ao[of _ 1]
    by (sep_auto simp: p2rel_def unat_lit_rel_def uint32_nat_rel_def
        nat_lit_rel_def br_def is_pos_code_def
        nat_of_uint32_0_iff nat_0_AND uint32_0_AND
        split: if_splits)+
  show ?thesis
    using 2[FCOMP 1] unfolding unat_lit_rel_def .
qed


subsubsection \<open>Unit Propagation: Step\<close>

definition delete_index_and_swap_update :: \<open>('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b list\<close> where
  \<open>delete_index_and_swap_update W K w = W(K := delete_index_and_swap (W K) w)\<close>

text \<open>The precondition is not necessary.\<close>
lemma delete_index_and_swap_ll_delete_index_and_swap_update:
  \<open>(uncurry2 (RETURN ooo delete_index_and_swap_ll), uncurry2 (RETURN ooo delete_index_and_swap_update))
  \<in>[\<lambda>((W, L), i). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f (\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<times>\<^sub>r nat_lit_rel) \<times>\<^sub>r nat_rel \<rightarrow>
      \<langle>\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<rangle>nres_rel\<close>
  by (auto simp: delete_index_and_swap_ll_def uncurry_def fref_def nres_rel_def
      delete_index_and_swap_update_def map_fun_rel_def p2rel_def nat_lit_rel_def br_def
      nth_list_update' nat_lit_rel_def
      simp del: literal_of_nat.simps)

definition append_update :: \<open>('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b list\<close> where
  \<open>append_update W L a = W(L:= W (L) @ [a])\<close>

lemma append_ll_append_update:
  \<open>(uncurry2 (RETURN ooo (\<lambda>xs i j. append_ll xs (nat_of_uint32 i) j)), uncurry2 (RETURN ooo append_update))
  \<in>  [\<lambda>((W, L), i). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f
     \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<times>\<^sub>f unat_lit_rel \<times>\<^sub>f Id \<rightarrow> \<langle>\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<rangle>nres_rel\<close>
  by (auto simp: append_ll_def uncurry_def fref_def nres_rel_def
      delete_index_and_swap_update_def map_fun_rel_def p2rel_def nat_lit_rel_def
      nth_list_update' append_update_def nat_lit_rel_def unat_lit_rel_def br_def
      uint32_nat_rel_def append_update_def
      simp del: literal_of_nat.simps)


definition is_decided_hd_trail_wl where
  \<open>is_decided_hd_trail_wl S = is_decided (hd (get_trail_wl S))\<close>

definition is_decided_hd_trail_wll :: \<open>nat twl_st_wl \<Rightarrow> bool nres\<close> where
  \<open>is_decided_hd_trail_wll = (\<lambda>(M, N, D, NE, UE, Q, W).
     RETURN (is_decided (hd M))
   )\<close>

lemma
  pair_nat_ann_lit_assn_Decided_Some:
    \<open>pair_nat_ann_lit_assn (Decided x1) (aba, Some x2) = false\<close> and
  pair_nat_ann_lit_assn_Propagated_None:
    \<open>pair_nat_ann_lit_assn (Propagated x21 x22) (aba, None) = false\<close>
  by (auto simp: nat_ann_lit_rel_def pure_def)

lemma Propagated_eq_ann_lit_of_pair_iff:
  \<open>Propagated x21 x22 = ann_lit_of_pair (a, b) \<longleftrightarrow> x21 = a \<and> b = Some x22\<close>
  by (cases b) auto

definition lit_and_ann_of_propagated_code where
  \<open>lit_and_ann_of_propagated_code = (\<lambda>L::ann_lit_wl. (fst L, the (snd L)))\<close>

lemma lit_and_ann_of_propagated_hnr[sepref_fr_rules]:
  \<open>(return o lit_and_ann_of_propagated_code, RETURN o lit_and_ann_of_propagated) \<in>
   [\<lambda>L. \<not>is_decided L]\<^sub>a pair_nat_ann_lit_assn\<^sup>k \<rightarrow> (unat_lit_assn *a nat_assn)\<close>
  unfolding lit_and_ann_of_propagated_code_def
  apply sepref_to_hoare
  apply (rename_tac x x')
  apply (case_tac x)
  by (sep_auto simp: nat_ann_lit_rel_def p2rel_def nat_lit_rel_def
      Propagated_eq_ann_lit_of_pair_iff unat_lit_rel_def uint32_nat_rel_def Collect_eq_comp
      br_def Collect_eq_comp nat_lit_rel_def
      simp del: literal_of_nat.simps)+

lemma set_mset_all_lits_of_mm_atms_of_ms_iff:
  \<open>set_mset (all_lits_of_mm A) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<longleftrightarrow> atms_of_ms (set_mset A) = atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
  by (force simp: atms_of_s_def in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def
      atms_of_def atm_of_eq_atm_of in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
      all_lits_of_mm_add_mset all_lits_of_m_add_mset
      eq_commute[of \<open>set_mset (all_lits_of_mm _)\<close> \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l _)\<close>]
      dest: multi_member_split)

definition card_max_lvl where
  \<open>card_max_lvl M C \<equiv> size (filter_mset (\<lambda>L. get_level M L = count_decided M) C)\<close>

lemma card_max_lvl_add_mset: \<open>card_max_lvl M (add_mset L C) =
  (if get_level M L = count_decided M then 1 else 0) +
    card_max_lvl M C\<close>
  by (auto simp: card_max_lvl_def)

lemma card_max_lvl_empty[simp]: \<open>card_max_lvl M {#} = 0\<close>
  by (auto simp: card_max_lvl_def)

lemma card_max_lvl_all_poss:
   \<open>card_max_lvl M C = card_max_lvl M (poss (atm_of `# C))\<close>
  unfolding card_max_lvl_def
  apply (induction C)
  subgoal by auto
  subgoal for L C
    using get_level_uminus[of M L]
    by (cases L) (auto)
  done

lemma card_max_lvl_distinct_cong:
  assumes
    \<open>\<And>L. get_level M (Pos L) = count_decided M \<Longrightarrow> (L \<in> atms_of C) \<Longrightarrow> (L \<in> atms_of C')\<close> and
    \<open>\<And>L. get_level M (Pos L) = count_decided M \<Longrightarrow> (L \<in> atms_of C') \<Longrightarrow> (L \<in> atms_of C)\<close> and
    \<open>distinct_mset C\<close> \<open>\<not>tautology C\<close> and
    \<open>distinct_mset C'\<close> \<open>\<not>tautology C'\<close>
  shows \<open>card_max_lvl M C = card_max_lvl M C'\<close>
proof -
  have [simp]: \<open>NO_MATCH (Pos x) L \<Longrightarrow> get_level M L = get_level M (Pos (atm_of L))\<close> for x L
    by (simp add: get_level_def)
  have [simp]: \<open>atm_of L \<notin> atms_of C' \<longleftrightarrow> L \<notin># C' \<and> -L \<notin># C'\<close> for L C'
    by (cases L) (auto simp: atm_iff_pos_or_neg_lit)
  then have [iff]: \<open>atm_of L \<in> atms_of C' \<longleftrightarrow> L \<in># C' \<or> -L \<in># C'\<close> for L C'
    by blast
  have H: \<open>distinct_mset {#L \<in># poss (atm_of `# C). get_level M L = count_decided M#}\<close>
    if \<open>distinct_mset C\<close> \<open>\<not>tautology C\<close> for C
    using that by (induction C) (auto simp: tautology_add_mset atm_of_eq_atm_of)
  show ?thesis
    apply (subst card_max_lvl_all_poss)
    apply (subst (2) card_max_lvl_all_poss)
    unfolding card_max_lvl_def
    apply (rule arg_cong[of _ _ size])
    apply (rule distinct_set_mset_eq)
    subgoal by (rule H) (use assms in fast)+
    subgoal by (rule H) (use assms in fast)+
    subgoal using assms by (auto simp: atms_of_def imageI image_iff) blast+
    done
qed


lemma Pos_unat_lit_assn:
  \<open>(return o (\<lambda>n. two_uint32 * n), RETURN o Pos) \<in> [\<lambda>L. Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> isasat_input_bounded \<A>]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
     unat_lit_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      nat_of_uint32_distrib_mult2)

lemma Neg_unat_lit_assn:
  \<open>(return o (\<lambda>n. two_uint32 * n +1), RETURN o Neg) \<in> [\<lambda>L. Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> isasat_input_bounded \<A>]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
      unat_lit_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      nat_of_uint32_distrib_mult2_plus1 uint_max_def)

lemma Pos_unat_lit_assn':
  \<open>(return o (\<lambda>n. two_uint32 * n), RETURN o Pos) \<in> [\<lambda>L. L \<le> uint_max div 2]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
     unat_lit_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      nat_of_uint32_distrib_mult2 uint_max_def)

lemma Neg_unat_lit_assn':
  \<open>(return o (\<lambda>n. two_uint32 * n + 1), RETURN o Neg) \<in> [\<lambda>L. L \<le> uint_max div 2]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
     unat_lit_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      nat_of_uint32_distrib_mult2 uint_max_def nat_of_uint32_add)

end
