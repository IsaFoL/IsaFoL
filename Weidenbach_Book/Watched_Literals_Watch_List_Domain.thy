theory Watched_Literals_Watch_List_Domain
  imports Watched_Literals_Watch_List
    Array_UInt
begin

text \<open>We refine the implementation by adding a \<^emph>\<open>domain\<close> on the literals\<close>

no_notation Ref.update ("_ := _" 62)

subsection \<open>State Conversion\<close>

subsubsection \<open>Functions and Types:\<close>

type_synonym ann_lits_l = \<open>(nat, nat) ann_lits\<close>
type_synonym clauses_to_update_ll = \<open>nat list\<close>
type_synonym lit_queue_l = \<open>uint32 list\<close>
type_synonym nat_trail = \<open>(uint32 \<times> nat option) list\<close>
type_synonym clause_wl = \<open>uint32 array\<close>
type_synonym unit_lits_wl = \<open>uint32 list list\<close>

type_synonym watched_wl = \<open>((nat \<times> uint32) array_list) array\<close>
type_synonym watched_wl_uint32 = \<open>((uint32 \<times> uint32) array_list) array\<close>


subsubsection \<open>Refinement of the Watched Function\<close>

definition map_fun_rel :: \<open>(nat \<times> 'key) set \<Rightarrow> ('b \<times> 'a) set \<Rightarrow> ('b list \<times> ('key \<Rightarrow> 'a)) set\<close> where
  map_fun_rel_def_internal:
    \<open>map_fun_rel D R = {(m, f). \<forall>(i, j)\<in>D. i < length m \<and> (m ! i, f j) \<in> R}\<close>

lemma map_fun_rel_def:
  \<open>\<langle>R\<rangle>map_fun_rel D = {(m, f). \<forall>(i, j)\<in>D. i < length m \<and> (m ! i, f j) \<in> R}\<close>
  unfolding relAPP_def map_fun_rel_def_internal by auto

definition map_fun_rel_assn
   :: \<open>(nat watcher) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> (nat literal \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> assn\<close>
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

definition lit_of_natP where
  \<open>lit_of_natP L L' \<longleftrightarrow> literal_of_nat L = L'\<close>

definition nat_lit_rel :: \<open>(nat watcher) set\<close> where
  \<open>nat_lit_rel \<equiv> {(n, L). lit_of_natP n L}\<close>

abbreviation nat_lit_assn :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> assn\<close> where
  \<open>nat_lit_assn \<equiv> pure nat_lit_rel\<close>

definition unat_lit_rel :: \<open>(uint32 \<times> nat literal) set\<close> where
  \<open>unat_lit_rel \<equiv> uint32_nat_rel O nat_lit_rel\<close>

abbreviation unat_lit_assn :: \<open>nat literal \<Rightarrow> uint32 \<Rightarrow> assn\<close> where
  \<open>unat_lit_assn \<equiv> pure unat_lit_rel\<close>

lemma hr_comp_uint32_nat_assn_nat_lit_rel[simp]:
  \<open>hr_comp uint32_nat_assn nat_lit_rel = unat_lit_assn\<close>
  by (auto simp: hrp_comp_def hr_comp_def uint32_nat_rel_def
        lit_of_natP_def hr_comp_pure br_def unat_lit_rel_def)

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

lemma lit_of_natP_nat_of_lit_iff: \<open>lit_of_natP c a \<longleftrightarrow> c = nat_of_lit a\<close>
  by (cases a) (auto simp: lit_of_natP_def)

lemma
   nat_lit_rel_right_unique: \<open>IS_RIGHT_UNIQUE nat_lit_rel\<close> and
   nat_lit_rel_left_unique: \<open>IS_LEFT_UNIQUE nat_lit_rel\<close>
  unfolding single_valued_def nat_lit_rel_def IS_LEFT_UNIQUE_def
  by (auto simp: lit_of_natP_nat_of_lit_iff)

term \<open>\<lambda>R R'. {(a, b). \<exists>c d. (fst a, c) \<in> R \<and> (snd a, d) \<in> R' \<and>
      b = ann_lit_of_pair (literal_of_nat c, d)}\<close>

definition ann_lit_rel:: \<open>('a \<times> nat) set \<Rightarrow> ('b \<times> nat option) set \<Rightarrow>
    (('a \<times> 'b) \<times> (nat, nat) ann_lit) set\<close> where
  ann_lit_rel_internal_def:
  \<open>ann_lit_rel R R' = {(a, b). \<exists>c d. (fst a, c) \<in> R \<and> (snd a, d) \<in> R' \<and>
      b = ann_lit_of_pair (literal_of_nat c, d)}\<close>

type_synonym ann_lit_wl = \<open>uint32 \<times> nat option\<close>
type_synonym ann_lits_wl = \<open>ann_lit_wl list\<close>
type_synonym ann_lit_wl_fast = \<open>uint32 \<times> uint32 option\<close>
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
  \<open>pair_nat_ann_lit_fast_assn \<equiv> hr_comp (uint32_assn *a option_assn uint32_nat_assn) nat_ann_lit_rel\<close>

abbreviation pair_nat_ann_lits_fast_assn :: \<open>(nat, nat) ann_lits \<Rightarrow> ann_lits_wl_fast \<Rightarrow> assn\<close> where
  \<open>pair_nat_ann_lits_fast_assn \<equiv> list_assn pair_nat_ann_lit_fast_assn\<close>

lemma nat_ann_lits_rel_Cons[iff]:
  \<open>(x # xs, y # ys) \<in> nat_ann_lits_rel \<longleftrightarrow> (x, y) \<in> nat_ann_lit_rel \<and> (xs, ys) \<in> nat_ann_lits_rel\<close>
  by (auto simp: nat_ann_lits_rel_def)

lemma lit_of_natP_same_rightD: \<open>lit_of_natP bi b \<Longrightarrow> lit_of_natP bi a \<Longrightarrow> a = b\<close>
  by (auto simp: p2rel_def lit_of_natP_def)

lemma lit_of_natP_same_leftD: \<open>lit_of_natP bi b \<Longrightarrow> lit_of_natP ai b \<Longrightarrow> ai = bi\<close>
  apply (auto simp: p2rel_def lit_of_natP_def split: if_splits)
  apply presburger
  done


subsubsection \<open>Code\<close>

lemma [sepref_fr_rules]: \<open>(return o id, RETURN o nat_of_lit) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: uint32_nat_rel_def br_def unat_lit_rel_def nat_lit_rel_def
      lit_of_natP_def)

definition (in -)the_is_empty where
  \<open>the_is_empty D = Multiset.is_empty (the D)\<close>


subsection \<open>Refinement\<close>

abbreviation uint_max :: nat where
  \<open>uint_max \<equiv> uint32_max\<close>

lemmas uint_max_def = uint32_max_def


text \<open>We start in a context where we have an initial set of atoms. \<close>
locale isasat_input_ops =
  fixes \<A>\<^sub>i\<^sub>n :: \<open>nat multiset\<close>
begin

text \<open>This is the \<^emph>\<open>completion\<close> of \<^term>\<open>\<A>\<^sub>i\<^sub>n\<close>, containing the positive and the negation of every
  literal of \<^term>\<open>\<A>\<^sub>i\<^sub>n\<close>:\<close>
definition \<L>\<^sub>a\<^sub>l\<^sub>l where \<open>\<L>\<^sub>a\<^sub>l\<^sub>l = poss \<A>\<^sub>i\<^sub>n + negs \<A>\<^sub>i\<^sub>n\<close>

lemma atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n: \<open>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l = set_mset \<A>\<^sub>i\<^sub>n\<close>
  unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_def by (auto simp: atms_of_def image_Un image_image)

definition is_\<L>\<^sub>a\<^sub>l\<^sub>l :: \<open>nat literal multiset \<Rightarrow> bool\<close> where
  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l S \<longleftrightarrow> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l = set_mset S\<close>
definition blits_in_\<L>\<^sub>i\<^sub>n :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>blits_in_\<L>\<^sub>i\<^sub>n S \<longleftrightarrow>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l. \<forall>(i, K) \<in> set (watched_by S L). K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>

definition literals_are_\<L>\<^sub>i\<^sub>n :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>literals_are_\<L>\<^sub>i\<^sub>n S \<equiv>
     is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm ((\<lambda>C. mset (fst C)) `# ran_m (get_clauses_wl S)
        + get_unit_clauses_wl S)) \<and>
     blits_in_\<L>\<^sub>i\<^sub>n S\<close>

definition literals_are_in_\<L>\<^sub>i\<^sub>n :: \<open>nat clause \<Rightarrow> bool\<close> where
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C \<longleftrightarrow> set_mset (all_lits_of_m C) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_empty[simp]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n {#}\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def)

lemma in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff: \<open>x \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<longleftrightarrow> atm_of x \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  by (cases x) (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def atms_of_def atm_of_eq_atm_of image_Un image_image)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (add_mset L A) \<longleftrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n A \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_mono:
  assumes N: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D'\<close> and D: \<open>D \<subseteq># D'\<close>
  shows \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D\<close>
proof -
  have \<open>set_mset (all_lits_of_m D) \<subseteq> set_mset (all_lits_of_m D')\<close>
    using D by (auto simp: in_all_lits_of_m_ain_atms_of_iff atm_iff_pos_or_neg_lit)
  then show ?thesis
     using N unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_def by fast
qed

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_sub:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n y \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n (y - z)\<close>
  using literals_are_in_\<L>\<^sub>i\<^sub>n_mono[of y \<open>y - z\<close>] by auto

lemma all_lits_of_m_subset_all_lits_of_mmD:
  \<open>a \<in># b \<Longrightarrow> set_mset (all_lits_of_m a) \<subseteq> set_mset (all_lits_of_mm b)\<close>
  by (auto simp: all_lits_of_m_def all_lits_of_mm_def)

lemma all_lits_of_m_remdups_mset:
  \<open>set_mset (all_lits_of_m (remdups_mset N)) = set_mset (all_lits_of_m N)\<close>
  by (auto simp: all_lits_of_m_def)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_remdups[simp]:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (remdups_mset N) = literals_are_in_\<L>\<^sub>i\<^sub>n N\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_remdups_mset)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_nth:
  fixes C :: nat
  assumes dom: \<open>C \<in># dom_m (get_clauses_wl S)\<close> and
   \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  shows \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S \<propto> C))\<close>
proof -
  let ?N = \<open>get_clauses_wl S\<close>
  have \<open>?N \<propto> C \<in># ran_mf ?N\<close>
    using dom by (auto simp: ran_m_def)
  then have \<open>mset (?N \<propto> C) \<in># mset `# (ran_mf ?N)\<close>
    by blast
  from all_lits_of_m_subset_all_lits_of_mmD[OF this] show ?thesis
    using assms(2) unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_in_\<L>\<^sub>i\<^sub>n_def literals_are_\<L>\<^sub>i\<^sub>n_def
    by (auto simp add: all_lits_of_mm_union)
qed

lemma uminus_\<A>\<^sub>i\<^sub>n_iff: \<open>- L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<longleftrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  by (simp add: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)

definition literals_are_in_\<L>\<^sub>i\<^sub>n_mm :: \<open>nat clauses \<Rightarrow> bool\<close> where
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm C \<longleftrightarrow> set_mset (all_lits_of_mm C) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l:
  assumes
    N1: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# ran_mf xs)\<close> and
    i_xs: \<open>i \<in># dom_m xs\<close> and j_xs: \<open>j < length (xs \<propto> i)\<close>
  shows \<open>xs \<propto> i ! j \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
proof -
  have \<open>xs \<propto> i \<in># ran_mf xs\<close>
    using i_xs by auto
  then have \<open>xs \<propto> i ! j \<in> set_mset (all_lits_of_mm (mset `# ran_mf xs))\<close>
    using j_xs by (auto simp: in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def Bex_def
      intro!: exI[of _ \<open>xs \<propto> i\<close>])
  then show ?thesis
    using N1 unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def by blast
qed

definition literals_are_in_\<L>\<^sub>i\<^sub>n_trail :: \<open>(nat, 'mark) ann_lits \<Rightarrow> bool\<close> where
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<longleftrightarrow> set_mset (lit_of `# mset M) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<Longrightarrow> a \<in> lits_of_l M \<Longrightarrow> a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def lits_of_def)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<Longrightarrow> a \<in> lits_of_l M \<Longrightarrow> atm_of a \<in># \<A>\<^sub>i\<^sub>n\<close>
  using literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l[of M a]
  unfolding in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[symmetric] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n[symmetric]
  .

lemma (in isasat_input_ops) literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (L # M) \<longleftrightarrow>
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and> lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def)

abbreviation D\<^sub>0 :: \<open>(nat watcher) set\<close> where
  \<open>D\<^sub>0 \<equiv> (\<lambda>L. (nat_of_lit L, L)) ` set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>

definition length_ll_f where
  \<open>length_ll_f W L = length (W L)\<close>

lemma length_ll_length_ll_f:
  \<open>(uncurry (RETURN oo length_ll), uncurry (RETURN oo length_ll_f)) \<in>
     [\<lambda>(W, L). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0) \<times>\<^sub>r nat_lit_rel) \<rightarrow>
       \<langle>nat_rel\<rangle> nres_rel\<close>
  unfolding length_ll_def length_ll_f_def
  by (fastforce simp: fref_def map_fun_rel_def prod_rel_def nres_rel_def p2rel_def lit_of_natP_def
      nat_lit_rel_def)

abbreviation array_watched_assn
  :: \<open>(nat literal \<Rightarrow> (nat\<times> nat literal) list) \<Rightarrow> ((nat \<times> uint32) array_list) array \<Rightarrow> assn\<close>
where
  \<open>array_watched_assn \<equiv> hr_comp (arrayO_assn (arl_assn (nat_assn *a unat_lit_assn))) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0)\<close>

lemma (in isasat_input_ops) literals_are_in_\<L>\<^sub>i\<^sub>n_trail_empty[simp]:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail []\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def)

lemma (in isasat_input_ops) literals_are_in_\<L>\<^sub>i\<^sub>n_Cons:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (a # M) \<longleftrightarrow> lit_of a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_trail M\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def)

lemma (in isasat_input_ops) literals_are_in_\<L>\<^sub>i\<^sub>n_trail_lit_of_mset:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M = literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M)\<close>
  by (induction M) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset literals_are_in_\<L>\<^sub>i\<^sub>n_Cons)

lemma ex_list_watched:
  fixes W :: \<open>nat literal \<Rightarrow> 'a list\<close>
  shows \<open>\<exists>aa. \<forall>x\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit x < length aa \<and> aa ! nat_of_lit x = W x\<close>
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
  have H: \<open>x \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow>
      length l \<ge> Suc (Max (nat_of_lit ` set_mset \<L>\<^sub>a\<^sub>l\<^sub>l)) \<Longrightarrow>
      fold_mset (\<lambda>L a. a[nat_of_lit L := W L]) l (remdups_mset \<L>\<^sub>a\<^sub>l\<^sub>l) ! nat_of_lit x = W x\<close>
    for x l
    unfolding \<L>\<^sub>a\<^sub>l\<^sub>l'_def[symmetric]
    apply (induction \<L>\<^sub>a\<^sub>l\<^sub>l' arbitrary: l)
    subgoal by simp
    subgoal for xa Ls l
      apply (case_tac \<open>(nat_of_lit ` set_mset Ls) = {}\<close>)
       apply (solves simp)
      apply (auto simp: less_Suc_eq_le length_fold)
      done
    done
  have H': \<open>aa ! nat_of_lit x = W x\<close> if \<open>x \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> for x
    using that unfolding aa_def D'_def
    by (auto simp: D'_def image_image remdups_mset_def[symmetric]
        less_Suc_eq_le intro!: H)
  have \<open>?P aa\<close>
    by (auto simp: D'_def image_image remdups_mset_def[symmetric]
        less_Suc_eq_le length_aa H')
  then show ?thesis
    by blast
qed

lemma length_aa_length_ll_f[sepref_fr_rules]:
  \<open>(uncurry length_aa_u, uncurry (RETURN oo length_ll_f)) \<in>
    [\<lambda>(W, L). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a
      array_watched_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have P: \<open>is_pure nat_assn\<close>
    by auto
  have H: \<open>(uncurry length_aa_u, uncurry (RETURN \<circ>\<circ> length_ll_f))
     \<in> [comp_PRE (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel)
     (\<lambda>(W, L). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l) (\<lambda>_ (xs, i). i < length xs)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     ((arrayO_assn (arl_assn (nat_assn *a unat_lit_assn)))\<^sup>k *\<^sub>a
                      uint32_nat_assn\<^sup>k)
                     (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r
                      nat_lit_rel) \<rightarrow> hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF length_aa_u_hnr length_ll_length_ll_f] .

  have 1: \<open>?pre' = ?pre\<close>
    using ex_list_watched
    by (fastforce simp: comp_PRE_def prod_rel_def_internal relAPP_def map_fun_rel_def[abs_def]
        p2rel_def lit_of_natP_def literal_of_neq_eq_nat_of_lit_eq_iff length_ll_def nat_lit_rel_def
        simp del: literal_of_nat.simps)

  have 2: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp by (auto simp: hrp_comp_def hr_comp_def)
  have 3: \<open>?f' = ?f\<close>
    by (auto simp: hrp_comp_def hr_comp_def)

  show ?thesis
    using H unfolding 1 2 3 .
qed


lemma literals_are_in_\<L>\<^sub>i\<^sub>n_in_mset_\<L>\<^sub>a\<^sub>l\<^sub>l:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C \<Longrightarrow> L \<in># C \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_def
  by (auto dest!: multi_member_split simp: all_lits_of_m_add_mset)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l:
  assumes
    N1: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset xs)\<close> and
    i_xs: \<open>i < length xs\<close>
  shows \<open>xs ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  using literals_are_in_\<L>\<^sub>i\<^sub>n_in_mset_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<open>mset xs\<close> \<open>xs!i\<close>] assms by auto

lemma in_literals_are_in_\<L>\<^sub>i\<^sub>n_in_D\<^sub>0:
  assumes \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D\<close> and \<open>L \<in># D\<close>
  shows \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  using assms by (cases L) (auto simp: image_image literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_def)

lemma is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm A) \<longleftrightarrow> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l = atms_of_mm A\<close>
  unfolding set_mset_set_mset_eq_iff is_\<L>\<^sub>a\<^sub>l\<^sub>l_def Ball_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
    in_all_lits_of_mm_ain_atms_of_iff
  by auto (metis literal.sel(2))+

lemma in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n:\<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<longleftrightarrow> atm_of L \<in># \<A>\<^sub>i\<^sub>n\<close>
  by (cases L) (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n S \<longleftrightarrow> atms_of S \<subseteq> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  apply (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_mm_union lits_of_def
       in_all_lits_of_m_ain_atms_of_iff in_all_lits_of_mm_ain_atms_of_iff atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
       atm_of_eq_atm_of uminus_\<A>\<^sub>i\<^sub>n_iff subset_iff in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
  apply (auto simp: atms_of_def)
  done

lemma (in isasat_input_ops)
  assumes
      x2_T: \<open>(x2, T) \<in> state_wl_l b\<close> and
      struct: \<open>twl_struct_invs U\<close> and
      T_U: \<open>(T, U) \<in> twl_st_l b'\<close>
  shows
    literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail:
      \<open>literals_are_\<L>\<^sub>i\<^sub>n x2 \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl x2)\<close>
     (is \<open>_\<Longrightarrow> ?trail\<close>) and
    literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_conflict:
      \<open>literals_are_\<L>\<^sub>i\<^sub>n x2 \<Longrightarrow> get_conflict_wl x2 \<noteq> None \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl x2))\<close> and
    conflict_not_tautology:
      \<open>get_conflict_wl x2 \<noteq> None \<Longrightarrow> \<not>tautology (the (get_conflict_wl x2))\<close>
proof -
  have
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of U)\<close> and
    M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of U)\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of U)\<close>
   using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
   by fast+

  show lits_trail: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl x2)\<close>
    if \<open>literals_are_\<L>\<^sub>i\<^sub>n x2\<close>
    using alien that x2_T T_U unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
      literals_are_\<L>\<^sub>i\<^sub>n_def
    by (subst (asm) all_clss_l_ran_m[symmetric])
     (auto simp: twl_st twl_st_l twl_st_wl all_lits_of_mm_union lits_of_def
        convert_lits_l_def image_image in_all_lits_of_mm_ain_atms_of_iff
        get_unit_clauses_wl_alt_def
        simp del: all_clss_l_ran_m)

  {
    assume conf: \<open>get_conflict_wl x2 \<noteq> None\<close>
    show lits_confl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl x2))\<close>
      if \<open>literals_are_\<L>\<^sub>i\<^sub>n x2\<close>
      using x2_T T_U alien that conf unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def
       cdcl\<^sub>W_restart_mset.no_strange_atm_def literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def
       literals_are_\<L>\<^sub>i\<^sub>n_def
      apply (subst (asm) all_clss_l_ran_m[symmetric])
      unfolding image_mset_union all_lits_of_mm_union
      by (auto simp add: twl_st twl_st_l twl_st_wl all_lits_of_mm_union lits_of_def
         image_image in_all_lits_of_mm_ain_atms_of_iff
        in_all_lits_of_m_ain_atms_of_iff
        get_unit_clauses_wl_alt_def
        simp del: all_clss_l_ran_m)

    have M_confl: \<open>get_trail_wl x2 \<Turnstile>as CNot (the (get_conflict_wl x2))\<close>
      using confl conf x2_T T_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      by (auto 5 5 simp: twl_st twl_st_l true_annots_def)
    moreover have n_d: \<open>no_dup (get_trail_wl x2)\<close>
      using M_lev x2_T T_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (auto simp: twl_st twl_st_l)
    ultimately show 4: \<open>\<not>tautology (the (get_conflict_wl x2))\<close>
      using n_d M_confl
      by (meson no_dup_consistentD tautology_decomp' true_annots_true_cls_def_iff_negation_in_model)
  }
qed

lemma (in isasat_input_ops) literals_are_in_\<L>\<^sub>i\<^sub>n_trail_atm_of:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<longleftrightarrow> atm_of ` lits_of_l M \<subseteq> set_mset \<A>\<^sub>i\<^sub>n\<close>
  apply (rule iffI)
  subgoal by (auto dest: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms)
  subgoal by (fastforce simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def lits_of_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
  done

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_poss_remdups_mset:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (poss (remdups_mset (atm_of `# C))) \<longleftrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n C\<close>
  by (induction C)
    (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff atm_of_eq_atm_of
      dest!: multi_member_split)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_negs_remdups_mset:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (negs (remdups_mset (atm_of `# C))) \<longleftrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n C\<close>
  by (induction C)
    (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff atm_of_eq_atm_of
      dest!: multi_member_split)

end


locale isasat_input_bounded =
  isasat_input_ops \<A>\<^sub>i\<^sub>n
  for \<A>\<^sub>i\<^sub>n :: \<open>nat multiset\<close> +
  assumes
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max: \<open>\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit L \<le> uint_max\<close>

locale isasat_input_bounded_nempty =
  isasat_input_bounded \<A>\<^sub>i\<^sub>n
  for \<A>\<^sub>i\<^sub>n :: \<open>nat multiset\<close> +
  assumes
    \<A>\<^sub>i\<^sub>n_nempty: \<open>\<A>\<^sub>i\<^sub>n \<noteq> {#}\<close>


context isasat_input_bounded
begin

lemma in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max': \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> nat_of_lit L \<le> uint_max\<close>
  using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max by auto

lemma in_\<A>\<^sub>i\<^sub>n_less_than_uint_max_div_2:
  \<open>L \<in># \<A>\<^sub>i\<^sub>n \<Longrightarrow> L \<le> uint_max div 2\<close>
  using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max'[of \<open>Neg L\<close>]
  unfolding Ball_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
  by (auto simp: uint_max_def)

lemma simple_clss_size_upper_div2':
  assumes
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C\<close> and
    dist: \<open>distinct_mset C\<close> and
    tauto: \<open>\<not>tautology C\<close> and
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max: \<open>\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit L < uint_max - 1\<close>
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
    then have \<open>L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using lits by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def atm_of_lit_in_atms_of
        in_all_lits_of_m_ain_atms_of_iff subset_iff)
    then have \<open>Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
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
   lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C\<close> and
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
    then have \<open>L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using lits by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def atm_of_lit_in_atms_of
        in_all_lits_of_m_ain_atms_of_iff subset_iff)
    then have \<open>Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
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
   lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C\<close> and
   dist: \<open>distinct_mset C\<close>
  shows \<open>size C \<le> uint_max + 2\<close>
proof -
  let ?posC = \<open>filter_mset is_pos C\<close>
  let ?negC = \<open>filter_mset is_neg C\<close>
  have C: \<open>C = ?posC + ?negC\<close>
    apply (subst multiset_partition[of _ is_pos])
    by auto
  have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n ?posC\<close>
    by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF lits]) auto
  moreover have \<open>distinct_mset ?posC\<close>
    by (rule distinct_mset_mono[OF _dist]) auto
  ultimately have pos: \<open>size ?posC \<le> 1 + uint_max div 2\<close>
    by (rule simple_clss_size_upper_div2) (auto simp: tautology_decomp)

  have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n ?negC\<close>
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
   lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C\<close> and
   dist: \<open>distinct_mset C\<close>
 shows \<open>size C < uint64_max\<close>
  using clss_size_uint_max[OF assms] by (auto simp: uint32_max_def uint64_max_def)

lemma clss_size_upper:
  assumes
   lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C\<close> and
   dist: \<open>distinct_mset C\<close> and
   in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max: \<open>\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit L < uint_max - 1\<close>
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
  have [simp]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (poss ?A)\<close> \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (negs ?A)\<close>
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

lemma in_\<L>\<^sub>a\<^sub>l\<^sub>l_Suc_le_uint_max: \<open>Pos xa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> Suc xa \<le> uint_max\<close>
  using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max by (auto simp: uint_max_def)

lemma length_trail_uint_max_div2:
  assumes
    M_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and n_d: \<open>no_dup M\<close>
  shows \<open>length M \<le> uint_max div 2 + 1\<close>
proof -
  have dist_atm_M: \<open>distinct_mset {#atm_of (lit_of x). x \<in># mset M#}\<close>
    using n_d by (metis distinct_mset_mset_distinct mset_map no_dup_def)
  have incl: \<open>atm_of `# lit_of `# mset M \<subseteq># remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using assms dist_atm_M
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l lits_of_def no_dup_distinct
        atm_of_eq_atm_of)

  have inj_on: \<open>inj_on nat_of_lit (set_mset (remdups_mset \<L>\<^sub>a\<^sub>l\<^sub>l))\<close>
    by (auto simp: inj_on_def)
  have H: \<open>xa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> atm_of xa \<le> uint_max div 2\<close> for xa
    using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max
    by (cases xa) (auto simp: uint_max_def)
  have \<open>remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l) \<subseteq># mset [0..< 1 + (uint_max div 2)]\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using H distinct_image_mset_inj[OF inj_on]
    by (force simp del: literal_of_nat.simps simp: distinct_mset_mset_set
        dest: le_neq_implies_less)+
  note _ = size_mset_mono[OF this]
  moreover have \<open>size (nat_of_lit `# remdups_mset \<L>\<^sub>a\<^sub>l\<^sub>l) = size (remdups_mset \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
    by simp
  ultimately have 2: \<open>size (remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l)) \<le> 1 + uint_max div 2\<close>
    by auto
  from size_mset_mono[OF incl] have 1: \<open>length M \<le> size (remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l))\<close>
    unfolding uint_max_def count_decided_def
    by (auto simp del: length_filter_le)
  with 2 show ?thesis
    by (auto simp: uint32_max_def)
qed


definition (in isasat_input_ops) unit_prop_body_wl_D_inv
  :: \<open>nat twl_st_wl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> bool\<close> where
\<open>unit_prop_body_wl_D_inv T' j w L \<longleftrightarrow>
    unit_prop_body_wl_inv T' j w L \<and> literals_are_\<L>\<^sub>i\<^sub>n T' \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l
  \<close>

text \<open>
  \<^item> should be the definition of \<^term>\<open>unit_prop_body_wl_find_unwatched_inv\<close>.
  \<^item> the distinctiveness should probably be only a property, not a part of the definition.
\<close>
definition (in -) unit_prop_body_wl_D_find_unwatched_inv where
\<open>unit_prop_body_wl_D_find_unwatched_inv f C S \<longleftrightarrow>
   unit_prop_body_wl_find_unwatched_inv f C S \<and>
   (f \<noteq> None \<longrightarrow> the f \<ge> 2 \<and> the f < length (get_clauses_wl S \<propto> C) \<and>
   get_clauses_wl S \<propto> C ! (the f) \<noteq> get_clauses_wl S \<propto> C ! 0  \<and>
   get_clauses_wl S \<propto> C ! (the f) \<noteq> get_clauses_wl S \<propto> C ! 1)\<close>


definition (in isasat_input_ops) unit_propagation_inner_loop_wl_loop_D_inv where
  \<open>unit_propagation_inner_loop_wl_loop_D_inv L = (\<lambda>(j, w, S).
      literals_are_\<L>\<^sub>i\<^sub>n S \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
      unit_propagation_inner_loop_wl_loop_inv L (j, w, S))\<close>

definition (in isasat_input_ops) unit_propagation_inner_loop_wl_loop_D_pre where
  \<open>unit_propagation_inner_loop_wl_loop_D_pre L = (\<lambda>(j, w, S).
     unit_propagation_inner_loop_wl_loop_D_inv L (j, w, S) \<and>
     unit_propagation_inner_loop_wl_loop_pre L (j, w, S))\<close>

definition (in isasat_input_ops) unit_propagation_inner_loop_body_wl_D
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat twl_st_wl \<Rightarrow>
    (nat \<times> nat \<times> nat twl_st_wl) nres\<close> where
  \<open>unit_propagation_inner_loop_body_wl_D L j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_D_pre L (j, w, S));
      let (C, K) = (watched_by S L) ! w;
      let S = keep_watch L j w S;
      ASSERT(unit_prop_body_wl_D_inv S j w L);
      let val_K = polarity (get_trail_wl S) K;
      if val_K = Some True
      then RETURN (j+1, w+1, S)
      else do { \<comment>\<open>Now the costly operations:\<close>
        if C \<notin># dom_m (get_clauses_wl S)
        then RETURN (j, w+1, S)
        else do {
          let i = (if ((get_clauses_wl S)\<propto>C) ! 0 = L then 0 else 1);
          let L' = ((get_clauses_wl S)\<propto>C) ! (1 - i);
          let val_L' = polarity (get_trail_wl S) L';
          if val_L' = Some True
          then update_blit_wl L C j w L' S
          else do {
            f \<leftarrow> find_unwatched_l (get_trail_wl S) (get_clauses_wl S \<propto>C);
            ASSERT (unit_prop_body_wl_D_find_unwatched_inv f C S);
            case f of
              None \<Rightarrow> do {
                if val_L' = Some False
                then do {RETURN (j+1, w+1, set_conflict_wl (get_clauses_wl S \<propto> C) S)}
                else do {RETURN (j+1, w+1, propagate_lit_wl L' C i S)}
              }
            | Some f \<Rightarrow> do {
                let K = get_clauses_wl S \<propto> C ! f;
                let val_L' = polarity (get_trail_wl S) K;
                if val_L' = Some True
                then update_blit_wl L C j w K S
                else update_clause_wl L C j w i f S
              }
          }
        }
      }
   }\<close>

thm unit_propagation_inner_loop_body_wl_def
declare Id_refine[refine_vcg del] refine0(5)[refine_vcg del]

lemma unit_prop_body_wl_D_inv_clauses_distinct_eq:
  assumes
    x[simp]: \<open>watched_by S K ! w = (x1, x2)\<close> and
    inv: \<open>unit_prop_body_wl_D_inv (keep_watch K i w S) i w K\<close> and
    y: \<open>y < length (get_clauses_wl S \<propto> (fst (watched_by S K ! w)))\<close> and
    w: \<open>fst(watched_by S K ! w) \<in># dom_m (get_clauses_wl (keep_watch K i w S))\<close> and
    y': \<open>y' < length (get_clauses_wl S \<propto> (fst (watched_by S K ! w)))\<close> and
    w_le: \<open>w < length (watched_by S K)\<close>
  shows \<open>get_clauses_wl S \<propto> x1 ! y =
     get_clauses_wl S \<propto> x1 ! y' \<longleftrightarrow> y = y'\<close> (is \<open>?eq \<longleftrightarrow> ?y\<close>)
proof
  assume eq: ?eq
  let ?S = \<open>keep_watch K i w S\<close>
  let ?C = \<open>fst (watched_by ?S K ! w)\<close>
  have dom: \<open>fst (watched_by (keep_watch K i w S) K ! w) \<in># dom_m (get_clauses_wl (keep_watch K i w S))\<close>
      \<open>fst (watched_by (keep_watch K i w S) K ! w) \<in># dom_m (get_clauses_wl S)\<close>
    using w_le assms by (auto simp: x twl_st_wl)
  obtain T U where
      ST: \<open>(?S, T) \<in> state_wl_l (Some (K, w))\<close> and
      TU: \<open>(set_clauses_to_update_l
              (clauses_to_update_l
                (remove_one_lit_from_wq ?C T) +
                {#?C#})
              (remove_one_lit_from_wq ?C T),
              U)
            \<in> twl_st_l (Some K)\<close> and
      struct_U: \<open>twl_struct_invs U\<close> and
      i_w: \<open>i \<le> w\<close> and
      w_le: \<open>w < length (watched_by (keep_watch K i w S) K)\<close>
    using inv w unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
      unit_prop_body_wl_inv_def unit_propagation_inner_loop_body_l_inv_def x fst_conv
    apply -
    apply (simp only: simp_thms dom)
    apply normalize_goal+
    by blast
  have \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of U)\<close>
    using struct_U unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then have \<open>distinct_mset_mset (mset `# ran_mf (get_clauses_wl S))\<close>
    using ST TU
    unfolding image_Un cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      all_clss_lf_ran_m[symmetric] image_mset_union
    by (auto simp: drop_Suc twl_st_wl twl_st_l twl_st)
  then have \<open>distinct (get_clauses_wl S \<propto> C)\<close> if \<open>C > 0\<close> and \<open>C \<in># dom_m (get_clauses_wl S)\<close>
     for C
     using that ST TU unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
       distinct_mset_set_def
     by (auto simp: nth_in_set_tl mset_take_mset_drop_mset cdcl\<^sub>W_restart_mset_state
      distinct_mset_set_distinct
       twl_st_wl twl_st_l twl_st)
  moreover have \<open>?C > 0\<close> and \<open>?C \<in># dom_m (get_clauses_wl S)\<close>
    using inv w unfolding unit_propagation_inner_loop_body_l_inv_def unit_prop_body_wl_D_inv_def
      unit_prop_body_wl_inv_def x apply -
      apply (simp only: simp_thms twl_st_wl x fst_conv dom)
      apply normalize_goal+
      apply (solves simp)
      apply (simp only: simp_thms twl_st_wl x fst_conv dom)
      done
  ultimately have \<open>distinct (get_clauses_wl S \<propto> ?C)\<close>
    by blast
  moreover have \<open>fst (watched_by (keep_watch K i w S) K ! w) = fst (watched_by S K ! w)\<close>
    using i_w w_le
    by (cases S; cases \<open>i=w\<close>) (auto simp: keep_watch_def)
  ultimately show ?y
    using y y' eq
    by (auto simp: nth_eq_iff_index_eq twl_st_wl x)
next
  assume ?y
  then show ?eq by blast
qed

lemma (in isasat_input_ops) blits_in_\<L>\<^sub>i\<^sub>n_keep_watch:
  assumes \<open>blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, f, g)\<close> and
    w:\<open>w < length (watched_by (a, b, c, d, e, f, g) K)\<close>
  shows \<open>blits_in_\<L>\<^sub>i\<^sub>n
          (a, b, c, d, e, f, g (K := g K[j := g K ! w]))\<close>
proof -
  let ?g = \<open>g (K := g K[j := g K ! w])\<close>
  have H: \<open>\<And>L i K. L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> (i, K) \<in>set (g L) \<Longrightarrow>
        K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using assms
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by blast
  have \<open> L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> (i, K') \<in>set (?g L) \<Longrightarrow>
        K' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> for L i K'
    using H[of L i K'] H[of L \<open>fst (g K ! w)\<close> \<open>snd (g K ! w)\<close>]
      nth_mem[OF w]
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by (cases \<open>j < length (g K)\<close>; cases \<open>g K ! w\<close>)
      (auto split: if_splits elim!: in_set_upd_cases)
  then show ?thesis
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by blast
qed

text \<open>We mark as safe intro rule, since we will always be in a case where the equivalence holds,
  although in general the equivalence does not hold.\<close>
lemma (in isasat_input_ops) literals_are_\<L>\<^sub>i\<^sub>n_keep_watch[twl_st_wl, simp, intro!]:
  \<open>literals_are_\<L>\<^sub>i\<^sub>n S \<Longrightarrow> w < length (watched_by S K) \<Longrightarrow> literals_are_\<L>\<^sub>i\<^sub>n (keep_watch K j w S)\<close>
  by (cases S) (auto simp: keep_watch_def literals_are_\<L>\<^sub>i\<^sub>n_def
      blits_in_\<L>\<^sub>i\<^sub>n_keep_watch)

lemma blits_in_\<L>\<^sub>i\<^sub>n_propagate:
  \<open>blits_in_\<L>\<^sub>i\<^sub>n (Propagated (x1aa \<propto> x1 ! Suc 0) x1 # x1b, x1aa
         (x1 \<hookrightarrow> swap (x1aa \<propto> x1) 0 (Suc 0)), None, x1c, x1d,
          add_mset (- x1aa \<propto> x1 ! Suc 0) x1e, x2e) \<longleftrightarrow>
  blits_in_\<L>\<^sub>i\<^sub>n (x1b, x1aa, None, x1c, x1d, x1e, x2e)\<close>
  \<open>blits_in_\<L>\<^sub>i\<^sub>n
        (Propagated (x1aa \<propto> x1 ! 0) x1 # x1b, x1aa, None, x1c, x1d,
         add_mset (- x1aa \<propto> x1 ! 0) x1e, x2e) \<longleftrightarrow>
  blits_in_\<L>\<^sub>i\<^sub>n (x1b, x1aa, None, x1c, x1d, x1e, x2e)\<close>
  \<open>K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> blits_in_\<L>\<^sub>i\<^sub>n
        (x1a, x1aa(x1' \<hookrightarrow> swap (x1aa \<propto> x1') n n'), None, x1c, x1d,
         x1e, x2e
         (x1aa \<propto> x1' ! n' :=
            x2e (x1aa \<propto> x1' ! n') @ [(x1', K)])) \<longleftrightarrow>
  blits_in_\<L>\<^sub>i\<^sub>n (x1a, x1aa, None, x1c, x1d,
         x1e, x2e)\<close>
  unfolding blits_in_\<L>\<^sub>i\<^sub>n_def
  by (auto split: if_splits)

lemma literals_are_\<L>\<^sub>i\<^sub>n_set_conflict_wl:
  \<open>literals_are_\<L>\<^sub>i\<^sub>n (set_conflict_wl D S) \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  by (cases S; auto simp: blits_in_\<L>\<^sub>i\<^sub>n_def literals_are_\<L>\<^sub>i\<^sub>n_def set_conflict_wl_def)

lemma (in isasat_input_ops) blits_in_\<L>\<^sub>i\<^sub>n_keep_watch':
  assumes K': \<open>K' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<close> and
    w:\<open>blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, f, g)\<close>
  shows \<open>blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, f, g (K := g K[j := (i, K')]))\<close>
proof -
  let ?g = \<open>g (K := g K[j := (i, K')])\<close>
  have H: \<open>\<And>L i K. L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> (i, K) \<in>set (g L) \<Longrightarrow>
        K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using assms
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by blast
  have \<open> L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> (i, K') \<in>set (?g L) \<Longrightarrow>
        K' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> for L i K'
    using H[of L i K'] K'
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by (cases \<open>j < length (g K)\<close>; cases \<open>g K ! w\<close>)
      (auto split: if_splits elim!: in_set_upd_cases)
  then show ?thesis
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by blast
qed

lemma unit_propagation_inner_loop_body_wl_D_spec:
  fixes S :: \<open>nat twl_st_wl\<close> and K :: \<open>nat literal\<close> and w :: nat
  assumes
    K: \<open>K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  shows \<open>unit_propagation_inner_loop_body_wl_D K j w S \<le>
      \<Down> {((j', n', T'), (j, n, T)). j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T'}
        (unit_propagation_inner_loop_body_wl K j w S)\<close>
proof -
  obtain M N D NE UE Q W where
    S: \<open>S = (M, N, D, NE, UE, Q, W)\<close>
    by (cases S)
  have f': \<open>(f, f') \<in> \<langle>Id\<rangle>option_rel\<close> if \<open>(f, f') \<in> Id\<close> for f f'
    using that by auto
  define find_unwatched_wl :: \<open>(nat,nat) ann_lits \<Rightarrow> _\<close> where
    \<open>find_unwatched_wl = find_unwatched_l\<close>
  let ?C = \<open>fst ((watched_by S K) ! w)\<close>
  have find_unwatched: \<open>find_unwatched_wl (get_trail_wl S) ((get_clauses_wl S)\<propto>D)
    \<le> \<Down> {(L, L'). L = L' \<and> (L \<noteq> None \<longrightarrow> the L < length ((get_clauses_wl S)\<propto>C) \<and> the L \<ge> 2)}
        (find_unwatched_l (get_trail_wl S) ((get_clauses_wl S)\<propto>C))\<close>
      (is \<open>_ \<le> \<Down> ?find_unwatched _\<close>)
    if \<open>C = D\<close>
    for C D and L and K and S
    unfolding find_unwatched_l_def find_unwatched_wl_def that
    by (auto simp: intro!: RES_refine)

  have propagate_lit_wl:
      \<open>((j+1, w + 1,
        propagate_lit_wl
         (get_clauses_wl S \<propto> x1a ! (1 - (if get_clauses_wl S \<propto> x1a ! 0 = K then 0 else 1)))
         x1a
         (if get_clauses_wl S \<propto> x1a ! 0 = K then 0 else 1)
          S),
       j+1, w + 1,
       propagate_lit_wl
        (get_clauses_wl S \<propto> x1 !
         (1 - (if get_clauses_wl S \<propto> x1 ! 0 = K then 0
               else 1)))
       x1
        (if get_clauses_wl S \<propto> x1 ! 0 = K then 0 else 1) S)
      \<in> {((j', n', T'), j, n, T).
         j' = j \<and>
         n' = n \<and>
         T = T' \<and>
         literals_are_\<L>\<^sub>i\<^sub>n T'}\<close>
  if \<open>unit_prop_body_wl_D_inv S j w K\<close> and \<open>\<not>x1 \<notin># dom_m (get_clauses_wl S)\<close> and
    \<open>(watched_by S K) ! w = (x1a, x2a)\<close> and
    \<open>(watched_by S K) ! w = (x1, x2)\<close>
  for f f' j S x1 x2 x1a x2a
  unfolding propagate_lit_wl_def S
  apply clarify
  apply refine_vcg
  using that \<A>\<^sub>i\<^sub>n
  by (auto simp: clauses_def unit_prop_body_wl_find_unwatched_inv_def
        mset_take_mset_drop_mset' S unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        ran_m_mapsto_upd unit_propagation_inner_loop_body_l_inv_def blits_in_\<L>\<^sub>i\<^sub>n_propagate
        state_wl_l_def image_mset_remove1_mset_if literals_are_\<L>\<^sub>i\<^sub>n_def)

  have update_clause_wl: \<open>update_clause_wl K x1' j w
     (if get_clauses_wl S \<propto> x1' ! 0 = K then 0 else 1) n S
    \<le> \<Down> {((j', n', T'), j, n, T). j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T'}
       (update_clause_wl K x1 j w
         (if get_clauses_wl S \<propto> x1 ! 0 = K then 0 else 1) n' S)\<close>
    if \<open>(n, n') \<in> Id\<close> and \<open>unit_prop_body_wl_D_inv S j w K\<close>
      \<open>(f, f') \<in> ?find_unwatched x1 S\<close> and
      \<open>f = Some n\<close> \<open>f' = Some n'\<close> and
      \<open>unit_prop_body_wl_D_find_unwatched_inv f x1' S\<close> and
      \<open>\<not>x1 \<notin># dom_m (get_clauses_wl S)\<close> and
      \<open>watched_by S K ! w = (x1, x2)\<close> and
      \<open>watched_by S K ! w = (x1', x2')\<close>
    for n n' f f' S x1 x2 x1' x2'
    unfolding update_clause_wl_def S
    apply refine_vcg
    using that \<A>\<^sub>i\<^sub>n
    by (auto simp: clauses_def mset_take_mset_drop_mset unit_prop_body_wl_find_unwatched_inv_def
          mset_take_mset_drop_mset' S unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
          ran_m_clause_upd unit_propagation_inner_loop_body_l_inv_def blits_in_\<L>\<^sub>i\<^sub>n_propagate
          state_wl_l_def image_mset_remove1_mset_if literals_are_\<L>\<^sub>i\<^sub>n_def)
  have H: \<open>watched_by S K ! w = A \<Longrightarrow> watched_by (keep_watch K j w S) K ! w = A\<close>
    for S j w K A x1
    by (cases S; cases \<open>j=w\<close>) (auto simp: keep_watch_def)
  have update_blit_wl: \<open>update_blit_wl K x1a j w
        (get_clauses_wl (keep_watch K j w S) \<propto> x1a !
          (1 -
          (if get_clauses_wl (keep_watch K j w S) \<propto> x1a ! 0 = K then 0 else 1)))
        (keep_watch K j w S)
        \<le> \<Down> {((j', n', T'), j, n, T).
            j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T'}
          (update_blit_wl K x1 j w
            (get_clauses_wl (keep_watch K j w S) \<propto> x1 !
              (1 -
              (if get_clauses_wl (keep_watch K j w S) \<propto> x1 ! 0 = K then 0
                else 1)))
            (keep_watch K j w S))\<close>
    if
      x: \<open>watched_by S K ! w = (x1, x2)\<close> and
      xa: \<open>watched_by S K ! w = (x1a, x2a)\<close> and
      unit: \<open>unit_prop_body_wl_D_inv (keep_watch K j w S) j w K\<close> and
      x1: \<open>\<not>x1 \<notin># dom_m (get_clauses_wl (keep_watch K j w S))\<close>
    for x1 x2 x1a x2a
  proof -
    have [simp]: \<open>x1a = x1\<close> and x1a: \<open>x1 \<in># dom_m (get_clauses_wl S)\<close>
      \<open>fst (watched_by (keep_watch K j w S) K ! w) \<in># dom_m (get_clauses_wl (keep_watch K j w S))\<close>
      using x xa x1 unit unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
      by auto

    have \<open>get_clauses_wl S \<propto>x1 ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> get_clauses_wl S \<propto>x1 ! Suc 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using assms that
        literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of x1 S]
        literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<open>get_clauses_wl S \<propto>x1\<close> 0]
        literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<open>get_clauses_wl S \<propto>x1\<close> 1]
      unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def x1a apply (simp only: x1a fst_conv simp_thms)
      apply normalize_goal+
      by (auto simp del:  simp: x1a)
    then show ?thesis
      using assms unit
      by (cases S) (auto simp: keep_watch_def update_blit_wl_def literals_are_\<L>\<^sub>i\<^sub>n_def
          blits_in_\<L>\<^sub>i\<^sub>n_propagate blits_in_\<L>\<^sub>i\<^sub>n_keep_watch' unit_prop_body_wl_D_inv_def)
  qed
  have update_blit_wl': \<open>update_blit_wl K x1a j w (get_clauses_wl (keep_watch K j w S) \<propto> x1a ! x)
        (keep_watch K j w S)
        \<le> \<Down> {((j', n', T'), j, n, T).
            j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T'}
          (update_blit_wl K x1 j w
            (get_clauses_wl (keep_watch K j w S) \<propto> x1 ! x')
            (keep_watch K j w S))\<close>
    if
      x1: \<open>watched_by S K ! w = (x1, x2)\<close> and
      xa: \<open>watched_by S K ! w = (x1a, x2a)\<close> and
      unw: \<open>unit_prop_body_wl_D_find_unwatched_inv f x1a (keep_watch K j w S)\<close> and
      dom: \<open>\<not>x1 \<notin># dom_m(get_clauses_wl (keep_watch K j w S))\<close> and
      unit: \<open>unit_prop_body_wl_D_inv (keep_watch K j w S) j w K\<close> and
      f: \<open>f = Some x\<close> and
      xx': \<open>(x, x') \<in> nat_rel\<close>
    for x1 x2 x1a x2a  f fa x x'
  proof -
    have [simp]: \<open>x1a = x1\<close> \<open>x = x'\<close>
      using x1 xa xx' by auto

    have x1a: \<open>x1 \<in># dom_m (get_clauses_wl S)\<close>
      \<open>fst (watched_by S K ! w) \<in># dom_m (get_clauses_wl S)\<close>
      using dom x1 by auto
    have \<open>get_clauses_wl S \<propto>x1 ! x \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using assms that
        literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of x1 S]
        literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<open>get_clauses_wl S \<propto>x1\<close> x]
         unw
      unfolding unit_prop_body_wl_D_find_unwatched_inv_def
      by auto
    then show ?thesis
      using assms
      by (cases S) (auto simp: keep_watch_def update_blit_wl_def literals_are_\<L>\<^sub>i\<^sub>n_def
          blits_in_\<L>\<^sub>i\<^sub>n_propagate blits_in_\<L>\<^sub>i\<^sub>n_keep_watch')
  qed

  have set_conflict_rel:
    \<open>((j + 1, w + 1,
        set_conflict_wl (get_clauses_wl (keep_watch K j w S) \<propto> x1a) (keep_watch K j w S)),
       j + 1, w + 1,
       set_conflict_wl (get_clauses_wl (keep_watch K j w S) \<propto> x1) (keep_watch K j w S))
      \<in> {((j', n', T'), j, n, T). j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T'}\<close>
    if
      pre: \<open>unit_propagation_inner_loop_wl_loop_D_pre K (j, w, S)\<close> and
      x: \<open>watched_by S K ! w = (x1, x2)\<close> and
      xa: \<open>watched_by S K ! w = (x1a, x2a)\<close> and
      unit: \<open>unit_prop_body_wl_D_inv (keep_watch K j w S) j w K\<close> and
      dom: \<open>\<not> x1a \<notin># dom_m (get_clauses_wl (keep_watch K j w S))\<close>
    for x1 x2 x1a x2a f fa
  proof -
    have [simp]: \<open>blits_in_\<L>\<^sub>i\<^sub>n
        (set_conflict_wl D (a, b, c, d, e, fb, g(K := g K[j := de]))) \<longleftrightarrow>
        blits_in_\<L>\<^sub>i\<^sub>n ((a, b, c, d, e, fb, g(K := g K[j := de])))\<close>
      for a b c d e f fb g de D
      by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n_def set_conflict_wl_def)

    have [simp]: \<open>x1a = x1\<close>
      using xa x by auto

    have \<open>x2a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using xa x dom assms pre unit nth_mem[of w \<open>watched_by S K\<close>]
      by (cases S)
        (auto simp: unit_prop_body_wl_D_inv_def literals_are_\<L>\<^sub>i\<^sub>n_def
          unit_prop_body_wl_inv_def blits_in_\<L>\<^sub>i\<^sub>n_def keep_watch_def
          unit_propagation_inner_loop_wl_loop_D_pre_def
          dest!: multi_member_split split: if_splits)
    then show ?thesis
      using assms that by (cases S) (auto simp: twl_st_wl keep_watch_def literals_are_\<L>\<^sub>i\<^sub>n_set_conflict_wl
          literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_keep_watch')
  qed
  show ?thesis
    unfolding unit_propagation_inner_loop_body_wl_D_def find_unwatched_wl_def[symmetric]
    unfolding unit_propagation_inner_loop_body_wl_def
    supply [[goals_limit=1]]
    apply (refine_rcg find_unwatched f')
    subgoal using assms unfolding unit_propagation_inner_loop_wl_loop_D_inv_def
        unit_propagation_inner_loop_wl_loop_D_pre_def unit_propagation_inner_loop_wl_loop_pre_def
      by auto
    subgoal using assms unfolding unit_prop_body_wl_D_inv_def
        unit_propagation_inner_loop_wl_loop_pre_def by auto
    subgoal by simp
    subgoal by (auto simp: unit_prop_body_wl_D_inv_def)
    subgoal by simp
    subgoal
      using assms by (auto simp: unit_prop_body_wl_D_inv_clauses_distinct_eq
          unit_propagation_inner_loop_wl_loop_pre_def)
    subgoal by simp
    subgoal by (rule update_blit_wl)
    subgoal by (auto simp: twl_st_wl)
    subgoal
      using assms
      unfolding unit_prop_body_wl_D_find_unwatched_inv_def unit_prop_body_wl_inv_def
      by (cases \<open>watched_by S K ! w\<close>)
        (auto simp: unit_prop_body_wl_D_inv_clauses_distinct_eq twl_st_wl)
    subgoal by (auto simp: twl_st_wl)
    subgoal by (auto simp: twl_st_wl)
    subgoal for x1 x2 x1a x2a f fa
      by (rule set_conflict_rel)
    subgoal by (rule propagate_lit_wl[OF _ _ H H])
    subgoal by (auto simp: twl_st_wl)
    subgoal by (rule update_blit_wl')
    subgoal by (rule update_clause_wl[OF _ _ _ _ _ _ _ H H])
    done
qed


lemma
  shows unit_propagation_inner_loop_body_wl_D_unit_propagation_inner_loop_body_wl_D:
  \<open>(uncurry3 unit_propagation_inner_loop_body_wl_D, uncurry3 unit_propagation_inner_loop_body_wl) \<in>
    [\<lambda>(((K, j), w), S). literals_are_\<L>\<^sub>i\<^sub>n S \<and> K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>f
    Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<rightarrow> \<langle>nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}\<rangle> nres_rel\<close>
     (is \<open>?G1\<close>) and
  unit_propagation_inner_loop_body_wl_D_unit_propagation_inner_loop_body_wl_D_weak:
   \<open>(uncurry3 unit_propagation_inner_loop_body_wl_D, uncurry3 unit_propagation_inner_loop_body_wl) \<in>
    [\<lambda>(((K, j), w), S). literals_are_\<L>\<^sub>i\<^sub>n S \<and> K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>f
    Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<rightarrow> \<langle>nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r Id\<rangle> nres_rel\<close>
   (is \<open>?G2\<close>)
proof -
  have 1: \<open>nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T} =
     {((j', n', T'), (j, (n, T))). j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T'}\<close>
    by auto
  show ?G1
    by (auto simp add: fref_def nres_rel_def uncurry_def simp del: twl_st_of_wl.simps
        intro!: unit_propagation_inner_loop_body_wl_D_spec[unfolded 1[symmetric]])
  then show ?G2
    apply -
    apply (match_spec)
    apply (match_fun_rel; match_fun_rel?)
    by fastforce+
qed

definition (in isasat_input_ops) unit_propagation_inner_loop_wl_loop_D
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat \<times> nat \<times> nat twl_st_wl) nres\<close>
where
  \<open>unit_propagation_inner_loop_wl_loop_D L S\<^sub>0 = do {
    WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_D_inv L\<^esup>
      (\<lambda>(j, w, S). w < length (watched_by S L) \<and> get_conflict_wl S = None)
      (\<lambda>(j, w, S). do {
        unit_propagation_inner_loop_body_wl_D L j w S
      })
      (0, 0, S\<^sub>0)
  }
  \<close>

lemma unit_propagation_inner_loop_wl_spec:
  assumes \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and K: \<open>K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  shows \<open>unit_propagation_inner_loop_wl_loop_D K S \<le>
     \<Down> {((j', n', T'), j, n, T). j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T'}
       (unit_propagation_inner_loop_wl_loop K S)\<close>
proof -
  have u: \<open>unit_propagation_inner_loop_body_wl_D K j w S \<le>
         \<Down> {((j', n', T'), j, n, T). j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T'}
           (unit_propagation_inner_loop_body_wl K' j' w' S')\<close>
  if \<open>K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    \<open>S = S'\<close> \<open>K = K'\<close> \<open>w = w'\<close> \<open>j'=j\<close>
  for S S' and w w' and K K' and j' j
    using unit_propagation_inner_loop_body_wl_D_spec[of K S j w] that by auto

  show ?thesis
    unfolding unit_propagation_inner_loop_wl_loop_D_def unit_propagation_inner_loop_wl_loop_def
    apply (refine_vcg u)
    subgoal using assms by auto
    subgoal using assms unfolding unit_propagation_inner_loop_wl_loop_D_inv_def by auto
    subgoal by auto
    subgoal using K by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition (in isasat_input_ops) unit_propagation_inner_loop_wl_D
 :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>unit_propagation_inner_loop_wl_D L S\<^sub>0 = do {
     (j, w, S) \<leftarrow> unit_propagation_inner_loop_wl_loop_D L S\<^sub>0;
     ASSERT (j \<le> w \<and> w \<le> length (watched_by S L) \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
     S \<leftarrow> cut_watch_list j w L S;
     RETURN S
  }\<close>

lemma unit_propagation_inner_loop_wl_D_spec:
  assumes \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and K: \<open>K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  shows \<open>unit_propagation_inner_loop_wl_D K S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
       (unit_propagation_inner_loop_wl K S)\<close>
proof -
  have cut_watch_list: \<open>cut_watch_list x1b x1c K x2c \<bind> RETURN
        \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
          (cut_watch_list x1 x1a K x2a)\<close>
    if
      \<open>(x, x')
      \<in> {((j', n', T'), j, n, T).
          j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T'}\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>x = (x1b, x2b)\<close> and
      \<open>x1 \<le> x1a \<and> x1a \<le> length (watched_by x2a K)\<close>
    for x x' x1 x2 x1a x2a x1b x2b x1c x2c
  proof -
    show ?thesis
      using that
      by (cases x2c) (auto simp: cut_watch_list_def literals_are_\<L>\<^sub>i\<^sub>n_def
          blits_in_\<L>\<^sub>i\<^sub>n_def dest!: in_set_takeD in_set_dropD)
  qed

  show ?thesis
    unfolding unit_propagation_inner_loop_wl_D_def unit_propagation_inner_loop_wl_def
    apply (refine_vcg unit_propagation_inner_loop_wl_spec)
    subgoal using \<A>\<^sub>i\<^sub>n .
    subgoal using K .
    subgoal by auto
    subgoal by auto
    subgoal using K by auto
    subgoal by (rule cut_watch_list)
    done
qed

definition (in isasat_input_ops)  unit_propagation_outer_loop_wl_D_inv where
\<open>unit_propagation_outer_loop_wl_D_inv S \<longleftrightarrow>
    unit_propagation_outer_loop_wl_inv S \<and>
    literals_are_\<L>\<^sub>i\<^sub>n S\<close>

definition (in isasat_input_ops) unit_propagation_outer_loop_wl_D
   :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>unit_propagation_outer_loop_wl_D S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>unit_propagation_outer_loop_wl_D_inv\<^esup>
      (\<lambda>S. literals_to_update_wl S \<noteq> {#})
      (\<lambda>S. do {
        ASSERT(literals_to_update_wl S \<noteq> {#});
        (S', L) \<leftarrow> select_and_remove_from_literals_to_update_wl S;
        ASSERT(L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl S') +
                        get_unit_clauses_wl S'));
        unit_propagation_inner_loop_wl_D L S'
      })
      (S\<^sub>0 :: nat twl_st_wl)\<close>

lemma literals_are_\<L>\<^sub>i\<^sub>n_set_lits_to_upd[twl_st_wl, simp]:
   \<open>literals_are_\<L>\<^sub>i\<^sub>n (set_literals_to_update_wl C S) \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  by (cases S) (auto simp: literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def)

lemma unit_propagation_outer_loop_wl_D_spec:
  assumes \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  shows \<open>unit_propagation_outer_loop_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
       (unit_propagation_outer_loop_wl S)\<close>
proof -
  have select: \<open>select_and_remove_from_literals_to_update_wl S \<le>
    \<Down> {((T', L'), (T, L)). T = T' \<and> L = L' \<and>
        T = set_literals_to_update_wl (literals_to_update_wl S - {#L#}) S}
              (select_and_remove_from_literals_to_update_wl S')\<close>
    if \<open>S = S'\<close> for S S' :: \<open>nat twl_st_wl\<close>
    unfolding select_and_remove_from_literals_to_update_wl_def select_and_remove_from_literals_to_update_def
    apply (rule RES_refine)
    using that unfolding select_and_remove_from_literals_to_update_wl_def by blast
  have unit_prop: \<open>literals_are_\<L>\<^sub>i\<^sub>n S \<Longrightarrow>
          K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow>
          unit_propagation_inner_loop_wl_D K S
          \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T} (unit_propagation_inner_loop_wl K' S')\<close>
    if \<open>K = K'\<close> and \<open>S = S'\<close> for K K' and S S' :: \<open>nat twl_st_wl\<close>
    unfolding that by (rule unit_propagation_inner_loop_wl_D_spec)
  show ?thesis
    unfolding unit_propagation_outer_loop_wl_D_def unit_propagation_outer_loop_wl_def
    apply (refine_vcg select unit_prop)
    subgoal using \<A>\<^sub>i\<^sub>n by simp
    subgoal unfolding unit_propagation_outer_loop_wl_D_inv_def by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using \<A>\<^sub>i\<^sub>n by (auto simp: twl_st_wl)
    subgoal for S' S T'L' TL T' L' T L
      by auto
        (auto simp add: is_\<L>\<^sub>a\<^sub>l\<^sub>l_def all_lits_of_mm_union 
          literals_are_\<L>\<^sub>i\<^sub>n_def)
    done
qed

lemma unit_propagation_outer_loop_wl_D_spec':
  shows \<open>(unit_propagation_outer_loop_wl_D, unit_propagation_outer_loop_wl) \<in> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T} \<rightarrow>\<^sub>f
     \<langle>{(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    apply (rule order_trans)
    apply (rule unit_propagation_outer_loop_wl_D_spec[of x])
     apply (auto simp: prod_rel_def intro: conc_fun_R_mono)
    done
  done

definition (in isasat_input_ops) skip_and_resolve_loop_wl_D_inv where
  \<open>skip_and_resolve_loop_wl_D_inv S\<^sub>0 brk S \<equiv>
      skip_and_resolve_loop_wl_inv S\<^sub>0 brk S \<and> literals_are_\<L>\<^sub>i\<^sub>n S\<close>

definition (in isasat_input_ops) skip_and_resolve_loop_wl_D
  :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>skip_and_resolve_loop_wl_D S\<^sub>0 =
    do {
      ASSERT(get_conflict_wl S\<^sub>0 \<noteq> None);
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S). skip_and_resolve_loop_wl_D_inv S\<^sub>0 brk S\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_wl S)))
        (\<lambda>(brk, S).
          do {
            ASSERT(\<not>brk \<and> \<not>is_decided (hd (get_trail_wl S)));
            let D' = the (get_conflict_wl S);
            let (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S));
            if -L \<notin># D' then
              do {RETURN (False, tl_state_wl S)}
            else
              if get_maximum_level (get_trail_wl S) (remove1_mset (-L) D') =
                count_decided (get_trail_wl S)
              then
                do {RETURN (update_confl_tl_wl C L S)}
              else
                do {RETURN (True, S)}
          }
        )
        (False, S\<^sub>0);
      RETURN S
    }
  \<close>

lemma (in isasat_input_ops) literals_are_\<L>\<^sub>i\<^sub>n_tl_state_wl[simp]:
  \<open>literals_are_\<L>\<^sub>i\<^sub>n (tl_state_wl S) = literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  by (cases S)
   (auto simp: is_\<L>\<^sub>a\<^sub>l\<^sub>l_def tl_state_wl_def literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def)

lemma (in isasat_input_ops) literals_are_\<L>\<^sub>i\<^sub>n_set_conflict_wl[simp]:
  \<open>literals_are_\<L>\<^sub>i\<^sub>n (set_conflict_wl D S) = literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  by (cases S)
   (auto simp: is_\<L>\<^sub>a\<^sub>l\<^sub>l_def set_conflict_wl_def literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def)

lemma get_clauses_wl_tl_state: \<open>get_clauses_wl (tl_state_wl T) = get_clauses_wl T\<close>
  unfolding tl_state_wl_def by (cases T) auto

lemma skip_and_resolve_loop_wl_D_spec:
  assumes \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  shows \<open>skip_and_resolve_loop_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T \<and> get_clauses_wl T = get_clauses_wl S}
       (skip_and_resolve_loop_wl S)\<close>
    (is \<open>_ \<le> \<Down> ?R _\<close>)
proof -
  define invar where
   \<open>invar = (\<lambda>(brk, T). skip_and_resolve_loop_wl_D_inv S brk T)\<close>
  have 1: \<open>((get_conflict_wl S = Some {#}, S), get_conflict_wl S = Some {#}, S) \<in> Id\<close>
    by auto


  show ?thesis
    unfolding skip_and_resolve_loop_wl_D_def skip_and_resolve_loop_wl_def H
    apply (subst (2) WHILEIT_add_post_condition)
    apply (refine_rcg 1 WHILEIT_refine[where R = \<open>{((i', S'), (i, S)). i = i' \<and> (S', S) \<in> ?R}\<close>])
    subgoal using assms by auto
    subgoal unfolding skip_and_resolve_loop_wl_D_inv_def by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by auto
    subgoal
      unfolding skip_and_resolve_loop_wl_D_inv_def update_confl_tl_wl_def
      by (auto split: prod.splits) (simp add: get_clauses_wl_tl_state)
    subgoal by auto
    subgoal
      unfolding skip_and_resolve_loop_wl_D_inv_def update_confl_tl_wl_def
      by (auto split: prod.splits simp: literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def)
    subgoal by auto
    subgoal by auto
    done
qed

definition find_lit_of_max_level_wl' :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow>
   nat literal nres\<close> where
  \<open>find_lit_of_max_level_wl' M N D NE UE Q W L =
     find_lit_of_max_level_wl (M, N, Some D, NE, UE, Q, W) L\<close>

definition (in -) list_of_mset2
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat clause \<Rightarrow> nat clause_l nres\<close>
where
  \<open>list_of_mset2 L L' D =
    SPEC (\<lambda>E. mset E = D \<and> E!0 = L \<and> E!1 = L' \<and> length E \<ge> 2)\<close>

definition (in -) single_of_mset where
  \<open>single_of_mset D = SPEC(\<lambda>L. D = mset [L])\<close>

definition (in isasat_input_ops) backtrack_wl_D_inv where
  \<open>backtrack_wl_D_inv S \<longleftrightarrow> backtrack_wl_inv S \<and> literals_are_\<L>\<^sub>i\<^sub>n S\<close>

definition (in isasat_input_ops) propagate_bt_wl_D
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>propagate_bt_wl_D = (\<lambda>L L' (M, N, D, NE, UE, Q, W). do {
    D'' \<leftarrow> list_of_mset2 (-L) L' (the D);
    i \<leftarrow> get_fresh_index_wl N (NE+UE) W;
    RETURN (Propagated (-L) i # M, fmupd i (D'', False) N,
          None, NE, UE, {#L#}, W(-L:= W (-L) @ [(i, L')], L':= W L' @ [(i, -L)]))
      })\<close>

definition (in isasat_input_ops) propagate_unit_bt_wl_D
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close>
where
  \<open>propagate_unit_bt_wl_D = (\<lambda>L (M, N, D, NE, UE, Q, W). do {
        D' \<leftarrow> single_of_mset (the D);
        RETURN (Propagated (-L) 0 # M, N, None, NE, add_mset {#D'#} UE, {#L#}, W)
    })\<close>

definition (in isasat_input_ops) backtrack_wl_D :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>backtrack_wl_D S =
    do {
      ASSERT(backtrack_wl_D_inv S);
      let L = lit_of (hd (get_trail_wl S));
      S \<leftarrow> extract_shorter_conflict_wl S;
      S \<leftarrow> find_decomp_wl L S;

      if size (the (get_conflict_wl S)) > 1
      then do {
        L' \<leftarrow> find_lit_of_max_level_wl S L;
        propagate_bt_wl_D L L' S
      }
      else do {
        propagate_unit_bt_wl_D L S
     }
  }\<close>

lemma backtrack_wl_D_spec:
  fixes S :: \<open>nat twl_st_wl\<close>
  assumes \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and confl: \<open>get_conflict_wl S ~= None\<close>
  shows \<open>backtrack_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
       (backtrack_wl S)\<close>
proof -
  have 1: \<open>((get_conflict_wl S = Some {#}, S), get_conflict_wl S = Some {#}, S) \<in> Id\<close>
    by auto

  have 3: \<open>find_lit_of_max_level_wl S M \<le>
   \<Down> {(L', L). L' \<in># remove1_mset (-M) (the (get_conflict_wl S)) \<and> L' = L} (find_lit_of_max_level_wl S' M')\<close>
    if \<open>S = S'\<close> and \<open>M = M'\<close>
    for S S' :: \<open>nat twl_st_wl\<close> and M M'
    using that by (cases S; cases S') (auto simp: find_lit_of_max_level_wl_def intro!: RES_refine)
  have H: \<open>mset `# mset (take n (tl xs)) + a + (mset `# mset (drop (Suc n) xs) + b) =
   mset `# mset (tl xs) + a + b\<close> for n and xs :: \<open>'a list list\<close> and a b
    apply (subst (2) append_take_drop_id[of n \<open>tl xs\<close>, symmetric])
    apply (subst mset_append)
    by (auto simp: drop_Suc)
  have list_of_mset: \<open>list_of_mset2 L L' D \<le>
      \<Down> {(E, F). F = [L, L'] @ remove1 L (remove1 L' E) \<and> D = mset E \<and> E!0 = L \<and> E!1 = L' \<and> E=F}
        (list_of_mset D')\<close>
    (is \<open>_ \<le> \<Down> ?list_of_mset _\<close>)
    if \<open>D = D'\<close> and uL_D: \<open>L \<in># D\<close> and L'_D: \<open>L' \<in># D\<close> and L_uL': \<open>L \<noteq> L'\<close> for D D' L L'
    unfolding list_of_mset_def list_of_mset2_def
  proof (rule RES_refine)
    fix s
    assume s: \<open>s \<in> {E. mset E = D \<and> E ! 0 = L \<and> E ! 1 = L' \<and> length E \<ge> 2}\<close>
    then show \<open>\<exists>s'\<in>{D'a. D' = mset D'a}.
            (s, s')
            \<in> {(E, F).
                F = [L, L'] @ remove1 L (remove1 L' E) \<and> D = mset E \<and> E ! 0 = L \<and> E ! 1 = L'\<and> E=F}\<close>
      apply (cases s; cases \<open>tl s\<close>)
      using that by (auto simp: diff_single_eq_union diff_diff_add_mset[symmetric]
          simp del: diff_diff_add_mset)
  qed

  define extract_shorter_conflict_wl' where
    \<open>extract_shorter_conflict_wl' S = extract_shorter_conflict_wl S\<close> for S :: \<open>nat twl_st_wl\<close>
  define find_lit_of_max_level_wl' where
    \<open>find_lit_of_max_level_wl' S = find_lit_of_max_level_wl S\<close> for S :: \<open>nat twl_st_wl\<close>

  have extract_shorter_conflict_wl: \<open>extract_shorter_conflict_wl' S
    \<le> \<Down> {(U, U'). U = U' \<and> equality_except_conflict_wl U S \<and> get_conflict_wl U \<noteq> None \<and>
      the (get_conflict_wl U) \<subseteq># the (get_conflict_wl S) \<and>
      -lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl U)
      } (extract_shorter_conflict_wl S)\<close>
    (is \<open>_ \<le> \<Down> ?extract_shorter _\<close>)
    unfolding extract_shorter_conflict_wl'_def extract_shorter_conflict_wl_def
    by (cases S)
      (auto 5 5 simp: extract_shorter_conflict_wl'_def extract_shorter_conflict_wl_def
       intro!: RES_refine)

  have find_decomp_wl: \<open>find_decomp_wl (lit_of (hd (get_trail_wl S))) T
    \<le> \<Down> {(U, U'). U = U' \<and> equality_except_trail_wl U T}
        (find_decomp_wl (lit_of (hd (get_trail_wl S))) T')\<close>
    (is \<open>_ \<le> \<Down> ?find_decomp _\<close>)
    if \<open>(T, T') \<in> ?extract_shorter\<close>
    for T T'
    using that unfolding find_decomp_wl_def
    by (cases T) (auto 5 5 intro!: RES_refine)

  have find_lit_of_max_level_wl:
    \<open>find_lit_of_max_level_wl U (lit_of (hd (get_trail_wl S)))
      \<le> \<Down> Id (find_lit_of_max_level_wl U' (lit_of (hd (get_trail_wl S))))\<close>
    if
      \<open>(U, U') \<in> ?find_decomp T\<close>
    for T U U'
    using that unfolding find_lit_of_max_level_wl_def
    by (cases T) (auto 5 5 intro!: RES_refine)

  have find_lit_of_max_level_wl':
     \<open>find_lit_of_max_level_wl' U (lit_of (hd (get_trail_wl S)))
        \<le> \<Down>{(L, L'). L = L' \<and> L \<in># remove1_mset (-lit_of (hd (get_trail_wl S))) (the (get_conflict_wl U))}
           (find_lit_of_max_level_wl U' (lit_of (hd (get_trail_wl S))))\<close>
      (is \<open>_ \<le> \<Down> ?find_lit _\<close>)
    if
      \<open>backtrack_wl_inv S\<close> and
      \<open>backtrack_wl_D_inv S\<close> and
      \<open>(U, U') \<in> ?find_decomp T\<close> and
      \<open>1 < size (the (get_conflict_wl U))\<close> and
      \<open>1 < size (the (get_conflict_wl U'))\<close>
    for U U' T
    using that unfolding find_lit_of_max_level_wl'_def find_lit_of_max_level_wl_def
    by (cases U) (auto 5 5 intro!: RES_refine)

  have is_\<L>\<^sub>a\<^sub>l\<^sub>l_add: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (A + B) \<longleftrightarrow> set_mset A \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close> if \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l B\<close> for A B
    using that unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto

  have propagate_bt_wl_D: \<open>propagate_bt_wl_D (lit_of (hd (get_trail_wl S))) L U
        \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
           (propagate_bt_wl (lit_of (hd (get_trail_wl S))) L' U')\<close>
    if
      \<open>backtrack_wl_inv S\<close> and
      bt: \<open>backtrack_wl_D_inv S\<close> and
      TT': \<open>(T, T') \<in> ?extract_shorter\<close> and
      UU': \<open>(U, U') \<in> ?find_decomp T\<close> and
      \<open>1 < size (the (get_conflict_wl U))\<close> and
      \<open>1 < size (the (get_conflict_wl U'))\<close> and
      LL': \<open>(L, L') \<in> ?find_lit U\<close>
    for L L' T T' U U'
  proof -
    obtain MS NS DS NES UES W Q where
       S: \<open>S = (MS, NS, Some DS, NES, UES, Q, W)\<close>
      using bt by (cases S; cases \<open>get_conflict_wl S\<close>)
        (auto simp: backtrack_wl_D_inv_def backtrack_wl_inv_def
          backtrack_l_inv_def state_wl_l_def)
    then obtain DT where
      T: \<open>T = (MS, NS, Some DT, NES, UES, Q, W)\<close> and DT: \<open>DT \<subseteq># DS\<close>
      using TT' by (cases T'; cases \<open>get_conflict_wl T'\<close>) auto
    then obtain MU where
      U: \<open>U = (MU, NS, Some DT, NES, UES, Q, W)\<close> and U': \<open>U' = U\<close>
      using UU' by (cases U) auto
    define list_of_mset where
      \<open>list_of_mset D L L' = ?list_of_mset D L L'\<close> for D and L L' :: \<open>nat literal\<close>
    have [simp]: \<open>get_conflict_wl S = Some DS\<close>
      using S by auto
    obtain T U where
      dist: \<open>distinct_mset (the (get_conflict_wl S))\<close> and
      ST: \<open>(S, T) \<in> state_wl_l None\<close> and
      TU: \<open>(T, U) \<in> twl_st_l None\<close> and
      alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close>
      using bt unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
      twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      apply -
      apply normalize_goal+
      by (auto simp: twl_st_wl twl_st_l twl_st)

    then have \<open>distinct_mset DT\<close>
      using DT unfolding S by (auto simp: distinct_mset_mono)
    then have [simp]: \<open>L \<noteq> -lit_of (hd MS)\<close>
      using LL' by (auto simp: U S dest: distinct_mem_diff_mset)

    have \<open>x \<in># all_lits_of_m (the (get_conflict_wl S)) \<Longrightarrow>
        x \<in># all_lits_of_mm ({#mset x. x \<in># ran_mf (get_clauses_wl S)#} + get_unit_clauses_wl S)\<close>
      for x
      using alien ST TU unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      all_clss_lf_ran_m[symmetric] set_mset_union
      by (auto simp: twl_st_wl twl_st_l twl_st in_all_lits_of_m_ain_atms_of_iff
        in_all_lits_of_mm_ain_atms_of_iff get_unit_clauses_wl_alt_def)
    then have \<open>x \<in># all_lits_of_m DS \<Longrightarrow>
        x \<in># all_lits_of_mm ({#mset x. x \<in># ran_mf NS#} + (NES + UES))\<close>
      for x
      by (simp add: S)
    then have H: \<open>x \<in># all_lits_of_m DT \<Longrightarrow>
        x \<in># all_lits_of_mm ({#mset x. x \<in># ran_mf NS#} + (NES + UES))\<close>
      for x
      using DT all_lits_of_m_mono by blast
    have propa_ref: \<open>((Propagated (- lit_of (hd (get_trail_wl S))) i # MU, fmupd i (D, False) NS,
      None, NES, UES, unmark (hd (get_trail_wl S)), W
      (- lit_of (hd (get_trail_wl S)) :=
         W (- lit_of (hd (get_trail_wl S))) @ [(i, L)],
       L := W L @ [(i, -lit_of (hd (get_trail_wl S)))])),
     Propagated (- lit_of (hd (get_trail_wl S))) i' # MU,
     fmupd i'
      ([- lit_of (hd (get_trail_wl S)), L'] @
       remove1 (- lit_of (hd (get_trail_wl S))) (remove1 L' D'),
       False)
      NS,
     None, NES, UES, unmark (hd (get_trail_wl S)), W
     (- lit_of (hd (get_trail_wl S)) :=
        W (- lit_of (hd (get_trail_wl S))) @ [(i', L')],
      L' := W L' @ [(i', - lit_of (hd (get_trail_wl S)))]))
    \<in> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}\<close>
      if
        DD': \<open>(D, D') \<in> list_of_mset (the (Some DT)) (- lit_of (hd (get_trail_wl S))) L\<close> and
        ii': \<open>(i, i') \<in> {(i, i'). i = i' \<and> i \<notin># dom_m NS}\<close>
      for i i' D D'
    proof -
      have [simp]: \<open>i = i'\<close> \<open>L = L'\<close> and i'_dom: \<open>i' \<notin># dom_m NS\<close>
        using ii' LL' by auto
      have
        D: \<open>D = [- lit_of (hd (get_trail_wl S)), L] @
          remove1 (- lit_of (hd (get_trail_wl S))) (remove1 L D')\<close> and
        DT_D: \<open>DT = mset D\<close>
        using DD' unfolding list_of_mset_def
        by force+
      have \<open>L \<in> set D\<close>
        using ii' LL' by (auto simp: U DT_D dest!: in_diffD)
      have K: \<open>L \<in> set D \<Longrightarrow> L \<in># all_lits_of_m (mset D)\<close> for L
        unfolding in_multiset_in_set[symmetric]
        apply (drule multi_member_split)
        by (auto simp: all_lits_of_m_add_mset)
      have [simp]: \<open>- lit_of (hd (get_trail_wl S)) # L' #
              remove1 (- lit_of (hd (get_trail_wl S))) (remove1 L' D') = D\<close>
        using D by simp
      then have 1[simp]: \<open>- lit_of (hd MS) # L' #
              remove1 (- lit_of (hd MS)) (remove1 L' D') = D\<close>
        using D by (simp add: S)
      have \<open>- lit_of (hd MS) \<in> set D\<close>
        apply (subst 1[symmetric])
        unfolding set_append list.sel
        by (rule list.set_intros)
      have \<open>x \<in># all_lits_of_mm ({#mset (fst x). x \<in># ran_m NS#} + (NES + UES)) \<Longrightarrow>
        x \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> for x
        using i'_dom \<A>\<^sub>i\<^sub>n is_\<L>\<^sub>a\<^sub>l\<^sub>l_def by (fastforce simp: S literals_are_\<L>\<^sub>i\<^sub>n_def)
      then show ?thesis
        using i'_dom \<A>\<^sub>i\<^sub>n K[OF \<open>L \<in> set D\<close>] K[OF \<open>- lit_of (hd MS) \<in> set D\<close>]
        by (auto simp: ran_m_mapsto_upd_notin all_lits_of_mm_add_mset literals_are_\<L>\<^sub>i\<^sub>n_def
            blits_in_\<L>\<^sub>i\<^sub>n_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_add S dest!: H[unfolded DT_D])
    qed
    define get_fresh_index2 where
      \<open>get_fresh_index2 N NUE W = get_fresh_index_wl (N :: nat clauses_l) (NUE :: nat clauses)
          (W::nat literal \<Rightarrow> (nat watcher) list)\<close>
      for N NUE W
    have fresh: \<open>get_fresh_index_wl N NUE W \<le> \<Down> {(i, i'). i = i' \<and> i \<notin># dom_m N} (get_fresh_index2 N' NUE' W')\<close>
      if \<open>N = N'\<close> \<open>NUE = NUE'\<close> \<open>W=W'\<close>for N N' NUE NUE' W W'
      using that by (auto simp: get_fresh_index_wl_def get_fresh_index2_def intro!: RES_refine)
    show ?thesis
      unfolding propagate_bt_wl_D_def propagate_bt_wl_def propagate_bt_wl_D_def U U' S T
      apply (subst (2) get_fresh_index2_def[symmetric])
      apply clarify
      apply (refine_rcg list_of_mset fresh)
      subgoal ..
      subgoal using TT' T by (auto simp: U S)
      subgoal using LL' by (auto simp: T U S dest: in_diffD)
      subgoal by auto
      subgoal ..
      subgoal ..
      subgoal ..
      subgoal for D D' i i'
        unfolding list_of_mset_def[symmetric] U[symmetric] U'[symmetric] S[symmetric] T[symmetric]
        by (rule propa_ref)
      done
  qed

  have propagate_unit_bt_wl_D: \<open>propagate_unit_bt_wl_D (lit_of (hd (get_trail_wl S))) U
    \<le> SPEC (\<lambda>c. (c, propagate_unit_bt_wl (lit_of (hd (get_trail_wl S))) U')
                 \<in> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T})\<close>
    if
      \<open>backtrack_wl_inv S\<close> and
      bt: \<open>backtrack_wl_D_inv S\<close> and
      TT': \<open>(T, T') \<in> ?extract_shorter\<close> and
      UU': \<open>(U, U') \<in> ?find_decomp T\<close> and
      \<open>\<not>1 < size (the (get_conflict_wl U))\<close> and
      \<open>\<not>1 < size (the (get_conflict_wl U'))\<close>
    for L L' T T' U U'
  proof -
    obtain MS NS DS NES UES W Q where
       S: \<open>S = (MS, NS, Some DS, NES, UES, Q, W)\<close>
      using bt by (cases S; cases \<open>get_conflict_wl S\<close>)
        (auto simp: backtrack_wl_D_inv_def backtrack_wl_inv_def
          backtrack_l_inv_def state_wl_l_def)
    then obtain DT where
      T: \<open>T = (MS, NS, Some DT, NES, UES, Q, W)\<close> and DT: \<open>DT \<subseteq># DS\<close>
      using TT' by (cases T'; cases \<open>get_conflict_wl T'\<close>) auto
    then obtain MU where
      U: \<open>U = (MU, NS, Some DT, NES, UES, Q, W)\<close> and U': \<open>U' = U\<close>
      using UU' by (cases U) auto
    define list_of_mset where
      \<open>list_of_mset D L L' = ?list_of_mset D L L'\<close> for D and L L' :: \<open>nat literal\<close>
    have [simp]: \<open>get_conflict_wl S = Some DS\<close>
      using S by auto
    obtain T U where
      dist: \<open>distinct_mset (the (get_conflict_wl S))\<close> and
      ST: \<open>(S, T) \<in> state_wl_l None\<close> and
      TU: \<open>(T, U) \<in> twl_st_l None\<close> and
      alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close>
      using bt unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
      twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      apply -
      apply normalize_goal+
      by (auto simp: twl_st_wl twl_st_l twl_st)

    then have \<open>distinct_mset DT\<close>
      using DT unfolding S by (auto simp: distinct_mset_mono)
    have \<open>x \<in># all_lits_of_m (the (get_conflict_wl S)) \<Longrightarrow>
        x \<in># all_lits_of_mm ({#mset x. x \<in># ran_mf (get_clauses_wl S)#} + get_unit_init_clss_wl S)\<close>
      for x
      using alien ST TU unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      all_clss_lf_ran_m[symmetric] set_mset_union
      by (auto simp: twl_st_wl twl_st_l twl_st in_all_lits_of_m_ain_atms_of_iff
        in_all_lits_of_mm_ain_atms_of_iff)
    then have \<open>x \<in># all_lits_of_m DS \<Longrightarrow>
        x \<in># all_lits_of_mm ({#mset x. x \<in># ran_mf NS#} + NES)\<close>
      for x
      by (simp add: S)
    then have H: \<open>x \<in># all_lits_of_m DT \<Longrightarrow>
        x \<in># all_lits_of_mm ({#mset x. x \<in># ran_mf NS#} + NES)\<close>
      for x
      using DT all_lits_of_m_mono by blast
    then have \<A>\<^sub>i\<^sub>n_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n DT\<close>
      using DT \<A>\<^sub>i\<^sub>n unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_def S is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_\<L>\<^sub>i\<^sub>n_def
      by (auto simp: all_lits_of_mm_union)

    show ?thesis
      unfolding propagate_unit_bt_wl_D_def propagate_unit_bt_wl_def U U' single_of_mset_def
      apply clarify
      apply refine_vcg
      using \<A>\<^sub>i\<^sub>n_D \<A>\<^sub>i\<^sub>n
      by (auto simp: clauses_def mset_take_mset_drop_mset mset_take_mset_drop_mset'
          all_lits_of_mm_add_mset is_\<L>\<^sub>a\<^sub>l\<^sub>l_add literals_are_in_\<L>\<^sub>i\<^sub>n_def S
          literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def)
  qed
  show ?thesis
    unfolding backtrack_wl_D_def backtrack_wl_def find_lit_of_max_level_wl'_def
      array_of_arl_def
    apply (subst extract_shorter_conflict_wl'_def[symmetric])
    apply (subst find_lit_of_max_level_wl'_def[symmetric])
    supply [[goals_limit=1]]
    apply (refine_vcg extract_shorter_conflict_wl find_lit_of_max_level_wl find_decomp_wl
       find_lit_of_max_level_wl' propagate_bt_wl_D propagate_unit_bt_wl_D)
    subgoal using \<A>\<^sub>i\<^sub>n unfolding backtrack_wl_D_inv_def by fast
    subgoal by auto
    by assumption+
qed


subsubsection \<open>Decide or Skip\<close>
thm find_unassigned_lit_wl_def
definition (in isasat_input_ops) find_unassigned_lit_wl_D
  :: \<open>nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> nat literal option) nres\<close>
where
  \<open>find_unassigned_lit_wl_D S = (
     SPEC(\<lambda>((M, N, D, NE, UE, WS, Q), L).
         S = (M, N, D, NE, UE, WS, Q) \<and>
         (L \<noteq> None \<longrightarrow>
            undefined_lit M (the L) \<and> the L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
            atm_of (the L) \<in> atms_of_mm (clause `# twl_clause_of `# init_clss_lf N + NE)) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit M L' \<and>
            atm_of L' \<in> atms_of_mm (clause `# twl_clause_of `# init_clss_lf N + NE)))))
\<close>


definition (in isasat_input_ops) decide_wl_or_skip_D_pre :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
\<open>decide_wl_or_skip_D_pre S \<longleftrightarrow>
   decide_wl_or_skip_pre S \<and> literals_are_\<L>\<^sub>i\<^sub>n S\<close>

definition(in isasat_input_ops)  decide_wl_or_skip_D
  :: \<open>nat twl_st_wl \<Rightarrow> (bool \<times> nat twl_st_wl) nres\<close>
where
  \<open>decide_wl_or_skip_D S = (do {
    ASSERT(decide_wl_or_skip_D_pre S);
    (S, L) \<leftarrow> find_unassigned_lit_wl_D S;
    case L of
      None \<Rightarrow> RETURN (True, S)
    | Some L \<Rightarrow> RETURN (False, decide_lit_wl L S)
  })
\<close>

theorem decide_wl_or_skip_D_spec:
  assumes \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  shows \<open>decide_wl_or_skip_D S
    \<le> \<Down> {((b', T'), b, T). b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T} (decide_wl_or_skip S)\<close>
proof -
  have H: \<open>find_unassigned_lit_wl_D S \<le> \<Down> {((S', L'), L). S' = S \<and> L = L' \<and>
         (L \<noteq> None \<longrightarrow>
            undefined_lit (get_trail_wl S) (the L) \<and>
            atm_of (the L) \<in> atms_of_mm (clause `# twl_clause_of `# init_clss_lf (get_clauses_wl S)
                 + get_unit_init_clss_wl S)) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit (get_trail_wl S) L' \<and>
            atm_of L' \<in> atms_of_mm (clause `# twl_clause_of `# init_clss_lf (get_clauses_wl S)
                 + get_unit_init_clss_wl S)))}
     (find_unassigned_lit_wl S')\<close>
    (is \<open>_ \<le> \<Down> ?find _\<close>)
    if \<open>S = S'\<close>
    for S S' :: \<open>nat twl_st_wl\<close>
    unfolding find_unassigned_lit_wl_def find_unassigned_lit_wl_D_def that
    by (cases S') (auto intro!: RES_refine simp: mset_take_mset_drop_mset')
  have [refine]: \<open>x = x' \<Longrightarrow> (x, x') \<in> \<langle>Id\<rangle> option_rel\<close>
    for x x' by auto
  have decide_lit_wl: \<open>((False, decide_lit_wl L T), False, decide_lit_wl L' S')
        \<in> {((b', T'), b, T).
            b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}\<close>
    if
      SS': \<open>(S, S') \<in> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}\<close> and
      \<open>decide_wl_or_skip_pre S'\<close> and
      pre: \<open>decide_wl_or_skip_D_pre S\<close> and
      LT_L': \<open>(LT, bL') \<in> ?find S\<close> and
      LT: \<open>LT = (T, bL)\<close> and
      \<open>bL' = Some L'\<close> and
      \<open>bL = Some L\<close> and
      LL': \<open>(L, L') \<in> Id\<close>
    for S S' L L' LT bL bL' T
  proof -
    have \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n T\<close> and [simp]: \<open>T = S\<close>
      using LT_L' pre unfolding LT decide_wl_or_skip_D_pre_def by fast+
    have [simp]: \<open>S' = S\<close> \<open>L = L'\<close>
      using SS' LL' by simp_all
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n (decide_lit_wl L' S)\<close>
      using \<A>\<^sub>i\<^sub>n
      by (cases S) (auto simp: decide_lit_wl_def clauses_def blits_in_\<L>\<^sub>i\<^sub>n_def
          literals_are_\<L>\<^sub>i\<^sub>n_def)
    then show ?thesis
      by auto
  qed

  have \<open>(decide_wl_or_skip_D, decide_wl_or_skip) \<in> {((T'), (T)).  T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T} \<rightarrow>\<^sub>f
     \<langle>{((b', T'), (b, T)). b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}\<rangle> nres_rel\<close>
    unfolding decide_wl_or_skip_D_def decide_wl_or_skip_def
    apply (intro frefI)
    apply (refine_vcg H)
    subgoal unfolding decide_wl_or_skip_D_pre_def by blast
    subgoal by simp
    subgoal by simp
    subgoal unfolding decide_wl_or_skip_D_pre_def by fast
    subgoal by (rule decide_lit_wl) assumption+
    done
  then show ?thesis
    using assms by (cases S) (auto simp: fref_def nres_rel_def)
qed

subsubsection \<open>Backtrack, Skip, Resolve or Decide\<close>

definition (in isasat_input_ops) cdcl_twl_o_prog_wl_D_pre where
\<open>cdcl_twl_o_prog_wl_D_pre S \<longleftrightarrow> cdcl_twl_o_prog_wl_pre S \<and> literals_are_\<L>\<^sub>i\<^sub>n S\<close>

definition (in isasat_input_ops) cdcl_twl_o_prog_wl_D
 :: \<open>nat twl_st_wl \<Rightarrow> (bool \<times> nat twl_st_wl) nres\<close>
where
  \<open>cdcl_twl_o_prog_wl_D S =
    do {
      ASSERT(cdcl_twl_o_prog_wl_D_pre S);
      if get_conflict_wl S = None
      then decide_wl_or_skip_D S
      else do {
        if count_decided (get_trail_wl S) > 0
        then do {
          T \<leftarrow> skip_and_resolve_loop_wl_D S;
          ASSERT(get_conflict_wl T \<noteq> None \<and> get_clauses_wl S = get_clauses_wl T);
          U \<leftarrow> backtrack_wl_D T;
          RETURN (False, U)
        }
        else RETURN (True, S)
      }
    }
  \<close>

theorem cdcl_twl_o_prog_wl_D_spec:
  assumes \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  shows \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), (b, T)). b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
     (cdcl_twl_o_prog_wl S)\<close>
proof -
  have 1: \<open>backtrack_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
       (backtrack_wl T)\<close> if \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and \<open>get_conflict_wl S ~= None\<close> and \<open>S = T\<close>
    for S T
    using backtrack_wl_D_spec[of S] that by fast
  have 2: \<open>skip_and_resolve_loop_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T \<and>  get_clauses_wl T = get_clauses_wl S}
        (skip_and_resolve_loop_wl T)\<close>
    if \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> \<open>S = T\<close>
    for S T
    using skip_and_resolve_loop_wl_D_spec[of S] that by fast
  show ?thesis
    using assms
    unfolding cdcl_twl_o_prog_wl_D_def cdcl_twl_o_prog_wl_def
    apply (refine_vcg decide_wl_or_skip_D_spec 1 2)
    subgoal unfolding cdcl_twl_o_prog_wl_D_pre_def by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by simp
    subgoal by auto
    subgoal by auto
    done
qed

theorem cdcl_twl_o_prog_wl_D_spec':
  shows
  \<open>(cdcl_twl_o_prog_wl_D, cdcl_twl_o_prog_wl) \<in>
    {(S,S'). (S,S') \<in> Id \<and>literals_are_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
    \<langle>bool_rel \<times>\<^sub>r {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    apply (rule order_trans)
    apply (rule cdcl_twl_o_prog_wl_D_spec[of x])
     apply (auto simp: prod_rel_def intro: conc_fun_R_mono)
    done
  done


subsubsection \<open>Full Strategy\<close>

definition (in isasat_input_ops) cdcl_twl_stgy_prog_wl_D
   :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>cdcl_twl_stgy_prog_wl_D S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T). cdcl_twl_stgy_prog_wl_inv S\<^sub>0 (brk, T)\<and>
          literals_are_\<L>\<^sub>i\<^sub>n T\<^esup>
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop_wl_D S;
          cdcl_twl_o_prog_wl_D T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>

theorem cdcl_twl_stgy_prog_wl_D_spec:
  assumes \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  shows \<open>cdcl_twl_stgy_prog_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
     (cdcl_twl_stgy_prog_wl S)\<close>
proof -
  have 1: \<open>((False, S), False, S) \<in> {((brk', T'), brk, T). brk = brk' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}\<close>
    using assms by fast
  have 2: \<open>unit_propagation_outer_loop_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
       (unit_propagation_outer_loop_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> for S T
    using unit_propagation_outer_loop_wl_D_spec[of S] that by fast
  have 3: \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), b, T). b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
    (cdcl_twl_o_prog_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> for S T
    using cdcl_twl_o_prog_wl_D_spec[of S] that by fast
  show ?thesis
    unfolding cdcl_twl_stgy_prog_wl_D_def cdcl_twl_stgy_prog_wl_def
    apply (refine_vcg 1 2 3)
    subgoal by auto
    subgoal by auto
    subgoal by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma cdcl_twl_stgy_prog_wl_D_spec':
  \<open>(cdcl_twl_stgy_prog_wl_D, cdcl_twl_stgy_prog_wl) \<in>
    {(S,S'). (S,S') \<in> Id \<and>literals_are_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
    \<langle>{(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto intro: cdcl_twl_stgy_prog_wl_D_spec)

definition (in isasat_input_ops) cdcl_twl_stgy_prog_wl_D_pre where
  \<open>cdcl_twl_stgy_prog_wl_D_pre S U \<longleftrightarrow>
    (cdcl_twl_stgy_prog_wl_pre S U \<and> literals_are_\<L>\<^sub>i\<^sub>n S)\<close>

lemma cdcl_twl_stgy_prog_wl_D_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_wl_D_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_prog_wl_D S \<le> \<Down> (state_wl_l None O twl_st_l None) (conclusive_TWL_run S')\<close>
proof -
  have T: \<open>cdcl_twl_stgy_prog_wl_pre S S' \<and> literals_are_\<L>\<^sub>i\<^sub>n S\<close>
    using assms unfolding cdcl_twl_stgy_prog_wl_D_pre_def by blast
  show ?thesis
    apply (rule order_trans[OF cdcl_twl_stgy_prog_wl_D_spec])
    subgoal using T by auto
    subgoal
      apply (rule order_trans)
      apply (rule ref_two_step')
       apply (rule cdcl_twl_stgy_prog_wl_spec_final[of _ S'])
      subgoal using T by fast
      subgoal unfolding conc_fun_chain by (rule conc_fun_R_mono) blast
      done
    done
qed


definition (in isasat_input_ops) cdcl_twl_stgy_prog_break_wl_D
   :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>cdcl_twl_stgy_prog_break_wl_D S\<^sub>0 =
  do {
    b \<leftarrow> SPEC (\<lambda>_. True);
    (b, brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(b, brk, T). cdcl_twl_stgy_prog_wl_inv S\<^sub>0 (brk, T) \<and>
          literals_are_\<L>\<^sub>i\<^sub>n T\<^esup>
        (\<lambda>(b, brk, _). b \<and> \<not>brk)
        (\<lambda>(b, brk, S).
        do {
          ASSERT(b);
          T \<leftarrow> unit_propagation_outer_loop_wl_D S;
          (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D T;
          b \<leftarrow> SPEC (\<lambda>_. True);
          RETURN(b, brk, T)
        })
        (b, False, S\<^sub>0);
    if brk then RETURN T
    else cdcl_twl_stgy_prog_wl_D T
  }\<close>

theorem cdcl_twl_stgy_prog_break_wl_D_spec:
  assumes \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  shows \<open>cdcl_twl_stgy_prog_break_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
     (cdcl_twl_stgy_prog_break_wl S)\<close>
proof -
  define f where \<open>f \<equiv> SPEC (\<lambda>_::bool. True)\<close>
  have 1: \<open>((b, False, S), b, False, S) \<in> {((b', brk', T'), b, brk, T). b = b' \<and> brk = brk' \<and>
        T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}\<close>
    for b
    using assms by fast
  have 1: \<open>((b, False, S), b', False, S) \<in> {((b', brk', T'), b, brk, T). b = b' \<and> brk = brk' \<and>
        T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}\<close>
    if \<open>(b, b') \<in> bool_rel\<close>
    for b b'
    using assms that by fast

  have 2: \<open>unit_propagation_outer_loop_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
       (unit_propagation_outer_loop_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> for S T
    using unit_propagation_outer_loop_wl_D_spec[of S] that by fast
  have 3: \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), b, T). b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
    (cdcl_twl_o_prog_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> for S T
    using cdcl_twl_o_prog_wl_D_spec[of S] that by fast
  show ?thesis
    unfolding cdcl_twl_stgy_prog_break_wl_D_def cdcl_twl_stgy_prog_break_wl_def f_def[symmetric]
    apply (refine_vcg 1 2 3)
    subgoal by auto
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by (fast intro!: cdcl_twl_stgy_prog_wl_D_spec)
    done
qed

lemma cdcl_twl_stgy_prog_break_wl_D_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_wl_D_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_prog_break_wl_D S \<le> \<Down> (state_wl_l None O twl_st_l None) (conclusive_TWL_run S')\<close>
proof -
  have T: \<open>cdcl_twl_stgy_prog_wl_pre S S' \<and> literals_are_\<L>\<^sub>i\<^sub>n S\<close>
    using assms unfolding cdcl_twl_stgy_prog_wl_D_pre_def by blast
  show ?thesis
    apply (rule order_trans[OF cdcl_twl_stgy_prog_break_wl_D_spec])
    subgoal using T by auto
    subgoal
      apply (rule order_trans)
      apply (rule ref_two_step')
       apply (rule cdcl_twl_stgy_prog_break_wl_spec_final[of _ S'])
      subgoal using T by fast
      subgoal unfolding conc_fun_chain by (rule conc_fun_R_mono) blast
      done
    done
qed

end \<comment> \<open>end of locale @{locale isasat_input_bounded}\<close>

end
