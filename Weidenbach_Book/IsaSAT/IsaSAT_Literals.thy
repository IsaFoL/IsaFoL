theory IsaSAT_Literals
  imports More_Sepref.WB_More_Refinement "HOL-Word.More_Word"
     Watched_Literals.Watched_Literals_Watch_List
     Entailment_Definition.Partial_Herbrand_Interpretation
     Isabelle_LLVM.Bits_Natural (*Watched_Literals.WB_Word*)
begin

chapter \<open>Refinement of Literals\<close>

section \<open>Literals as Natural Numbers\<close>

subsection \<open>Definition\<close>

lemma Pos_div2_iff:
  \<open>Pos ((bb :: nat) div 2) = b \<longleftrightarrow> is_pos b \<and> (bb = 2 * atm_of b \<or> bb = 2 * atm_of b + 1)\<close>
  by (cases b) auto
lemma Neg_div2_iff:
  \<open>Neg ((bb :: nat) div 2) = b \<longleftrightarrow> is_neg b \<and> (bb = 2 * atm_of b \<or> bb = 2 * atm_of b + 1)\<close>
  by (cases b) auto

text \<open>
  Modeling \<^typ>\<open>nat literal\<close> via the transformation associating \<^term>\<open>2*n\<close> or \<^term>\<open>2*n+1\<close>
  has some advantages over the transformation to positive or negative integers: 0 is not an issue.
  It is also a bit faster according to Armin Biere.
\<close>
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

lemma ex_literal_of_nat: \<open>\<exists>bb. b = literal_of_nat bb\<close>
  by (cases b)
    (auto simp: nat_of_lit_def split: if_splits; presburger; fail)+


subsection \<open>Lifting to annotated literals\<close>

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

definition ann_lit_rel:: \<open>('a \<times> nat) set \<Rightarrow> ('b \<times> nat option) set \<Rightarrow>
    (('a \<times> 'b) \<times> (nat, nat) ann_lit) set\<close> where
  ann_lit_rel_internal_def:
  \<open>ann_lit_rel R R' = {(a, b). \<exists>c d. (fst a, c) \<in> R \<and> (snd a, d) \<in> R' \<and>
      b = ann_lit_of_pair (literal_of_nat c, d)}\<close>


section \<open>Conflict Clause\<close>

definition the_is_empty where
  \<open>the_is_empty D = Multiset.is_empty (the D)\<close>


section \<open>Atoms with bound\<close>

definition uint32_max :: nat where
  \<open>uint32_max \<equiv> 2^32-1\<close>

definition uint64_max :: nat where
  \<open>uint64_max \<equiv> 2^64-1\<close>

definition sint32_max :: nat where
  \<open>sint32_max \<equiv> 2^31-1\<close>

definition sint64_max :: nat where
  \<open>sint64_max \<equiv> 2^63-1\<close>
  

lemma uint64_max_uint_def: \<open>unat (-1 :: 64 Word.word) = uint64_max\<close>
proof -
  have \<open>unat (-1 :: 64 Word.word) = unat (- Numeral1 :: 64 Word.word)\<close>
    unfolding numeral.numeral_One ..
  also have \<open>\<dots> = uint64_max\<close>
    unfolding unat_bintrunc_neg
    apply (simp add: uint64_max_def)
    apply (subst numeral_eq_Suc; subst bintrunc.Suc; simp)+
    done
  finally show ?thesis .
qed


section \<open>Operations with set of atoms.\<close>

context
  fixes \<A>\<^sub>i\<^sub>n :: \<open>nat multiset\<close>
begin

abbreviation D\<^sub>0 :: \<open>(nat \<times> nat literal) set\<close> where
  \<open>D\<^sub>0 \<equiv> (\<lambda>L. (nat_of_lit L, L)) ` set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)\<close>

definition length_ll_f where
  \<open>length_ll_f W L = length (W L)\<close>

text \<open>
  The following lemma was necessary at some point to prove the existence of a watch list.
\<close>
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
  [simp]: \<open>isasat_input_bounded = (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n. nat_of_lit L \<le> uint32_max)\<close>

definition isasat_input_nempty where
  [simp]: \<open>isasat_input_nempty = (set_mset \<A>\<^sub>i\<^sub>n \<noteq> {})\<close>

definition isasat_input_bounded_nempty where
  \<open>isasat_input_bounded_nempty = (isasat_input_bounded \<and> isasat_input_nempty)\<close>


section \<open>Set of atoms with bound\<close>

context
  assumes in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint32_max: \<open>isasat_input_bounded\<close>
begin

lemma in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint32_max': \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n \<Longrightarrow> nat_of_lit L \<le> uint32_max\<close>
  using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint32_max by auto

lemma in_\<A>\<^sub>i\<^sub>n_less_than_uint32_max_div_2:
  \<open>L \<in># \<A>\<^sub>i\<^sub>n \<Longrightarrow> L \<le> uint32_max div 2\<close>
  using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint32_max'[of \<open>Neg L\<close>]
  unfolding Ball_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
  by (auto simp: uint32_max_def)

lemma simple_clss_size_upper_div2':
  assumes
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n  \<A>\<^sub>i\<^sub>n C\<close> and
    dist: \<open>distinct_mset C\<close> and
    tauto: \<open>\<not>tautology C\<close> and
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint32_max: \<open>\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n. nat_of_lit L < uint32_max - 1\<close>
  shows \<open>size C \<le> uint32_max div 2\<close>
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
  have m: \<open>set_mset ?C \<subseteq> {0..<uint32_max div 2}\<close>
  proof
    fix L
    assume \<open>L \<in> set_mset ?C\<close>
    then have \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)\<close>
    using lits by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def atm_of_lit_in_atms_of
        in_all_lits_of_m_ain_atms_of_iff subset_iff)
    then have \<open>Pos L \<in># (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)\<close>
      using lits by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    then have \<open>nat_of_lit (Pos L) < uint32_max - 1\<close>
      using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint32_max by (auto simp: atm_of_lit_in_atms_of
        in_all_lits_of_m_ain_atms_of_iff subset_iff)
    then have \<open>L < uint32_max div 2\<close>
       by (auto simp: atm_of_lit_in_atms_of
        in_all_lits_of_m_ain_atms_of_iff subset_iff uint32_max_def)
    then show \<open>L \<in> {0..<uint32_max div 2}\<close>
       by (auto simp: atm_of_lit_in_atms_of uint32_max_def
        in_all_lits_of_m_ain_atms_of_iff subset_iff)
  qed
  moreover have \<open>card \<dots> =  uint32_max div 2\<close>
    by auto
  ultimately have \<open>card (set_mset ?C) \<le> uint32_max div 2\<close>
    using card_mono[OF _ m] by auto
  then show ?thesis
    unfolding card[symmetric] size .
qed


lemma simple_clss_size_upper_div2:
  assumes
   lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n  \<A>\<^sub>i\<^sub>n C\<close> and
   dist: \<open>distinct_mset C\<close> and
   tauto: \<open>\<not>tautology C\<close>
  shows \<open>size C \<le> 1 + uint32_max div 2\<close>
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
  have m: \<open>set_mset ?C \<subseteq> {0..uint32_max div 2}\<close>
  proof
    fix L
    assume \<open>L \<in> set_mset ?C\<close>
    then have \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l  \<A>\<^sub>i\<^sub>n)\<close>
    using lits by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def atm_of_lit_in_atms_of
        in_all_lits_of_m_ain_atms_of_iff subset_iff)
    then have \<open>Neg L \<in># (\<L>\<^sub>a\<^sub>l\<^sub>l  \<A>\<^sub>i\<^sub>n)\<close>
      using lits by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    then have \<open>nat_of_lit (Neg L) \<le> uint32_max\<close>
      using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint32_max by (auto simp: atm_of_lit_in_atms_of
        in_all_lits_of_m_ain_atms_of_iff subset_iff)
    then have \<open>L \<le> uint32_max div 2\<close>
       by (auto simp: atm_of_lit_in_atms_of
        in_all_lits_of_m_ain_atms_of_iff subset_iff uint32_max_def)
    then show \<open>L \<in> {0 .. uint32_max div 2}\<close>
       by (auto simp: atm_of_lit_in_atms_of uint32_max_def
        in_all_lits_of_m_ain_atms_of_iff subset_iff)
  qed
  moreover have \<open>card \<dots> =  1 + uint32_max div 2\<close>
    by auto
  ultimately have \<open>card (set_mset ?C) \<le> 1 + uint32_max div 2\<close>
    using card_mono[OF _ m] by auto
  then show ?thesis
    unfolding card[symmetric] size .
qed

lemma clss_size_uint32_max:
  assumes
   lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n C\<close> and
   dist: \<open>distinct_mset C\<close>
  shows \<open>size C \<le> uint32_max + 2\<close>
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
  ultimately have pos: \<open>size ?posC \<le> 1 + uint32_max div 2\<close>
    by (rule simple_clss_size_upper_div2) (auto simp: tautology_decomp)

  have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n ?negC\<close>
    by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF lits]) auto
  moreover have \<open>distinct_mset ?negC\<close>
    by (rule distinct_mset_mono[OF _dist]) auto
  ultimately have neg: \<open>size ?negC \<le> 1 + uint32_max div 2\<close>
    by (rule simple_clss_size_upper_div2) (auto simp: tautology_decomp)

  show ?thesis
    apply (subst C)
    apply (subst size_union)
    using pos neg by linarith
qed

lemma clss_size_upper:
  assumes
   lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n C\<close> and
   dist: \<open>distinct_mset C\<close> and
   in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint32_max: \<open>\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n. nat_of_lit L < uint32_max - 1\<close>
 shows \<open>size C \<le> uint32_max\<close>
proof -
  let ?A = \<open>remdups_mset (atm_of `# C)\<close>
  have [simp]: \<open>distinct_mset (poss ?A)\<close> \<open>distinct_mset (negs ?A)\<close>
    by (simp_all add: distinct_image_mset_inj inj_on_def)

  have \<open>C \<subseteq># poss ?A + negs ?A\<close>
    apply (rule distinct_subseteq_iff[THEN iffD1])
    subgoal by (auto simp: dist distinct_mset_add disjunct_not_in)
    subgoal
      apply rule
      using literal.exhaust_sel by (auto simp: image_iff )
    done
  have [simp]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n (poss ?A)\<close> \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n (negs ?A)\<close>
    using lits
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_negs_remdups_mset literals_are_in_\<L>\<^sub>i\<^sub>n_poss_remdups_mset)

  have \<open>\<not> tautology (poss ?A)\<close> \<open>\<not> tautology (negs ?A)\<close>
    by (auto simp: tautology_decomp)
  then have \<open>size (poss ?A) \<le> uint32_max div 2\<close> and \<open>size (negs ?A) \<le> uint32_max div 2\<close>
    using simple_clss_size_upper_div2'[of \<open>poss ?A\<close>]
      simple_clss_size_upper_div2'[of \<open>negs ?A\<close>] in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint32_max
    by auto
  then have \<open>size C \<le> uint32_max div 2 + uint32_max div 2\<close>
    using \<open>C \<subseteq># poss (remdups_mset (atm_of `# C)) + negs (remdups_mset (atm_of `# C))\<close>
      size_mset_mono by fastforce
  then show ?thesis by (auto simp: uint32_max_def)
qed

lemma
  assumes
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A>\<^sub>i\<^sub>n M\<close> and
    n_d: \<open>no_dup M\<close>
  shows
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_length_le_uint32_max:
      \<open>length M \<le> Suc (uint32_max div 2)\<close> and
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_count_decided_uint32_max:
      \<open>count_decided M \<le> Suc (uint32_max div 2)\<close> and
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint32_max:
      \<open>get_level M L \<le> Suc (uint32_max div 2)\<close>
proof -
  have \<open>length M = card (atm_of ` lits_of_l M)\<close>
    using no_dup_length_eq_card_atm_of_lits_of_l[OF n_d] .
  moreover have \<open>atm_of ` lits_of_l M \<subseteq> set_mset \<A>\<^sub>i\<^sub>n\<close>
    using lits unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_trail_atm_of by auto
  ultimately have \<open>length M \<le> card (set_mset \<A>\<^sub>i\<^sub>n)\<close>
    by (simp add: card_mono)
  moreover {
    have \<open>set_mset \<A>\<^sub>i\<^sub>n \<subseteq> {0 ..< (uint32_max div 2) + 1}\<close>
      using in_\<A>\<^sub>i\<^sub>n_less_than_uint32_max_div_2 by (fastforce simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
          Ball_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n uint32_max_def)
    from subset_eq_atLeast0_lessThan_card[OF this] have \<open>card (set_mset \<A>\<^sub>i\<^sub>n) \<le> uint32_max div 2 + 1\<close>
      .
  }
  ultimately show \<open>length M \<le> Suc (uint32_max div 2)\<close>
    by linarith
  moreover have \<open>count_decided M \<le> length M\<close>
    unfolding count_decided_def by auto
  ultimately show \<open>count_decided M \<le> Suc (uint32_max div 2)\<close> by simp
  then show \<open>get_level M L \<le> Suc (uint32_max div 2)\<close>
    using count_decided_ge_get_level[of M L]
    by simp
qed

lemma length_trail_uint32_max_div2:
  fixes M :: \<open>(nat, 'b) ann_lits\<close>
  assumes
    M_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n\<close> and
    n_d: \<open>no_dup M\<close>
  shows \<open>length M \<le> uint32_max div 2 + 1\<close>
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
  have H: \<open>xa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n \<Longrightarrow> atm_of xa \<le> uint32_max div 2\<close> for xa
    using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint32_max
    by (cases xa) (auto simp: uint32_max_def)
  have \<open>remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n) \<subseteq># mset [0..< 1 + (uint32_max div 2)]\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using H distinct_image_mset_inj[OF inj_on]
    by (force simp del: literal_of_nat.simps simp: distinct_mset_mset_set
        dest: le_neq_implies_less)+
  note _ = size_mset_mono[OF this]
  moreover have \<open>size (nat_of_lit `# remdups_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)) = size (remdups_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n))\<close>
    by simp
  ultimately have 2: \<open>size (remdups_mset (atm_of `# (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n))) \<le> 1 + uint32_max div 2\<close>
    by auto
  from size_mset_mono[OF incl] have 1: \<open>length M \<le> size (remdups_mset (atm_of `# (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)))\<close>
    unfolding uint32_max_def count_decided_def
    by (auto simp del: length_filter_le)
  with 2 show ?thesis
    by (auto simp: uint32_max_def)
qed

end

end


section \<open>Instantion for code generation\<close>
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


subsection \<open>Literals as Natural Numbers\<close>

definition propagated where
  \<open>propagated L C = (L, Some C)\<close>

definition decided where
  \<open>decided L = (L, None)\<close>

definition uminus_lit_imp :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>uminus_lit_imp L = bitXOR L 1\<close>

lemma uminus_lit_imp_uminus:
  \<open>(RETURN o uminus_lit_imp, RETURN o uminus) \<in>
     nat_lit_rel \<rightarrow>\<^sub>f \<langle>nat_lit_rel\<rangle>nres_rel\<close>
  unfolding bitXOR_1_if_mod_2 uminus_lit_imp_def
  by (intro frefI nres_relI) (auto simp: uminus_lit_imp_def case_prod_beta p2rel_def
      br_def nat_lit_rel_def split: option.splits, presburger)


subsection \<open>State Conversion\<close>

subsubsection \<open>Functions and Types:\<close>


subsubsection \<open>More Operations\<close>

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

definition get_maximum_level_remove where
  \<open>get_maximum_level_remove M D L =  get_maximum_level M (remove1_mset L D)\<close>

lemma in_list_all2_ex_in: \<open>a \<in> set xs \<Longrightarrow> list_all2 R xs ys \<Longrightarrow> \<exists>b \<in> set ys. R a b\<close>
  apply (subgoal_tac \<open>length xs = length ys\<close>)
   apply (rotate_tac 2)
   apply (induction xs ys rule: list_induct2)
    apply ((solves auto)+)[2]
  using list_all2_lengthD by blast

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

lemma hd_decided_count_decided_ge_1:
  \<open>x \<noteq> [] \<Longrightarrow> is_decided (hd x) \<Longrightarrow> Suc 0 \<le> count_decided x\<close>
  by (cases x) auto

definition (in -) find_decomp_wl_imp' :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clause_l list \<Rightarrow> nat \<Rightarrow>
    nat clause \<Rightarrow> nat clauses \<Rightarrow> nat clauses \<Rightarrow> nat lit_queue_wl \<Rightarrow>
    (nat literal \<Rightarrow> nat watched) \<Rightarrow> _ \<Rightarrow> (nat, nat) ann_lits nres\<close> where
  \<open>find_decomp_wl_imp' = (\<lambda>M N U D NE UE W Q L. find_decomp_wl_imp M D L)\<close>

definition is_decided_hd_trail_wl where
  \<open>is_decided_hd_trail_wl S = is_decided (hd (get_trail_wl S))\<close>

definition is_decided_hd_trail_wll :: \<open>nat twl_st_wl \<Rightarrow> bool nres\<close> where
  \<open>is_decided_hd_trail_wll = (\<lambda>(M, N, D, NE, UE, Q, W).
     RETURN (is_decided (hd M))
   )\<close>

lemma Propagated_eq_ann_lit_of_pair_iff:
  \<open>Propagated x21 x22 = ann_lit_of_pair (a, b) \<longleftrightarrow> x21 = a \<and> b = Some x22\<close>
  by (cases b) auto

lemma set_mset_all_lits_of_mm_atms_of_ms_iff:
  \<open>set_mset (all_lits_of_mm A) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<longleftrightarrow> atms_of_ms (set_mset A) = atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
  by (force simp add:  atms_of_s_def in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def
      atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n atms_of_def atm_of_eq_atm_of uminus_\<A>\<^sub>i\<^sub>n_iff
       eq_commute[of \<open>set_mset (all_lits_of_mm _)\<close> \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l _)\<close>]
    dest: multi_member_split)


section \<open>Polarities\<close>

type_synonym tri_bool = \<open>bool option\<close>

definition UNSET :: \<open>tri_bool\<close> where
  [simp]: \<open>UNSET = None\<close>

definition SET_FALSE :: \<open>tri_bool\<close> where
  [simp]: \<open>SET_FALSE = Some False\<close>

definition SET_TRUE :: \<open>tri_bool\<close> where
  [simp]: \<open>SET_TRUE = Some True\<close>

definition (in -) tri_bool_eq :: \<open>tri_bool \<Rightarrow> tri_bool \<Rightarrow> bool\<close> where
  \<open>tri_bool_eq = (=)\<close>


end
