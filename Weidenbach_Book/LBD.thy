theory LBD
  imports IsaSAT_Literals
begin

subsubsection \<open>LBD\<close>

text \<open>LBD (literal block distance) or glue is a measure of usefulness of clauses: It is the number
of different levels involved in a clause. This measure has been introduced by Glucose in 2009
(Audemart and Simon).

LBD has also another advantage, explaining why we implemented it even before working on restarts: It
can speed the conflict minimisation. Indeed a literal might be redundant only if there is a literal
of the same level in the conflict.

The LBD data structure is well-suited to do so: We mark every level that appears in the conflict in
a hash-table like data structure.
\<close>

paragraph \<open>Types and relations\<close>
type_synonym lbd = \<open>bool list\<close>
type_synonym lbd_ref = \<open>bool list \<times> nat \<times> nat\<close>
type_synonym lbd_assn = \<open>bool array \<times> uint32 \<times> uint32\<close>

abbreviation lbd_int_assn :: \<open>lbd_ref \<Rightarrow> lbd_assn \<Rightarrow> assn\<close> where
  \<open>lbd_int_assn \<equiv> array_assn bool_assn *a uint32_nat_assn *a uint32_nat_assn\<close>

text \<open>Beside the actual ``lookup'' table, we also keep the highest level marked so far to unmark
all levels faster (but we currently don't save the LBD and have to iterate over the data structure).
We also handle growing of the structure by hand instead of using a proper hash-table. We do so,
because there are much stronger guarantees on the key that there is in a general hash-table
(especially, our numbers are all small).
\<close>
definition lbd_ref where
  \<open>lbd_ref = {((lbd, n, m), lbd'). lbd = lbd' \<and> n < length lbd \<and>
      (\<forall>k > n. k < length lbd \<longrightarrow> \<not>lbd!k) \<and>
      length lbd \<le> Suc (Suc (uint_max div 2)) \<and> n < length lbd \<and>
      m = length (filter id lbd)}\<close>

definition lbd_assn :: \<open>lbd \<Rightarrow> lbd_assn \<Rightarrow> assn\<close> where
  \<open>lbd_assn \<equiv> hr_comp lbd_int_assn lbd_ref\<close>


paragraph \<open>Testing if a level is marked\<close>

definition level_in_lbd :: \<open>nat \<Rightarrow> lbd \<Rightarrow> bool\<close> where
  \<open>level_in_lbd i = (\<lambda>lbd. i < length lbd \<and> lbd!i)\<close>

definition level_in_lbd_ref :: \<open>nat \<Rightarrow> lbd_ref \<Rightarrow> bool\<close> where
  \<open>level_in_lbd_ref = (\<lambda>i (lbd, _). i < length_uint32_nat lbd \<and> lbd!i)\<close>

lemma level_in_lbd_ref_level_in_lbd:
  \<open>(uncurry (RETURN oo level_in_lbd_ref), uncurry (RETURN oo level_in_lbd)) \<in>
    nat_rel \<times>\<^sub>r lbd_ref \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: level_in_lbd_ref_def level_in_lbd_def lbd_ref_def)

sepref_definition level_in_lbd_code
  is \<open>uncurry (RETURN oo level_in_lbd_ref)\<close>
  :: \<open>[\<lambda>(n, (lbd, m)). length lbd \<le> uint_max]\<^sub>a
       uint32_nat_assn\<^sup>k *\<^sub>a lbd_int_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding level_in_lbd_ref_def short_circuit_conv
  by sepref


lemma level_in_lbd_hnr[sepref_fr_rules]:
  \<open>(uncurry level_in_lbd_code, uncurry (RETURN \<circ>\<circ> level_in_lbd)) \<in> uint32_nat_assn\<^sup>k *\<^sub>a
     lbd_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply lbd_ref_def[simp] uint_max_def[simp]
  using level_in_lbd_code.refine[FCOMP level_in_lbd_ref_level_in_lbd]
  unfolding lbd_assn_def .


paragraph \<open>Marking more levels\<close>
definition list_grow where
  \<open>list_grow xs n x = xs @ replicate (n - length xs) x\<close>

lemma list_grow_array_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 (\<lambda>xs u. array_grow xs (nat_of_uint32 u)),
        uncurry2 (RETURN ooo list_grow)) \<in>
    [\<lambda>((xs, n), x). n \<ge> length xs]\<^sub>a (array_assn R)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>d *\<^sub>a R\<^sup>k \<rightarrow>
       array_assn R\<close>
proof -
  obtain R' where [simp]:
    \<open>R = pure R'\<close>
    \<open>the_pure R = R'\<close>
    using assms by (metis CONSTRAINT_D pure_the_pure)
  have [simp]: \<open>pure R' b bi = \<up>( (bi, b) \<in> R')\<close> for b bi
    by (auto simp: pure_def)
  show ?thesis
    by sepref_to_hoare
       (sep_auto simp: list_grow_def array_assn_def is_array_def
          hr_comp_def list_rel_pres_length list_rel_def list_all2_replicate
         uint32_nat_rel_def br_def
        intro!: list_all2_appendI)
qed

definition lbd_write :: \<open>lbd \<Rightarrow> nat \<Rightarrow> lbd\<close> where
  \<open>lbd_write = (\<lambda>lbd i.
    (if i < length_uint32_nat lbd then (lbd[i := True])
     else ((list_grow lbd (i + 1) False)[i := True])))\<close>


definition lbd_ref_write :: \<open>lbd_ref \<Rightarrow> nat \<Rightarrow> lbd_ref nres\<close>  where
  \<open>lbd_ref_write = (\<lambda>(lbd, m, n) i. do {
    ASSERT(length lbd \<le> uint_max \<and> n + 1 \<le> uint_max);
    (if i < length_uint32_nat lbd then
       let n = if lbd ! i then n else n+one_uint32_nat in
       RETURN (lbd[i := True], max i m, n)
     else do {
        ASSERT(i + 1 \<le> uint_max);
        RETURN ((list_grow lbd (i + one_uint32_nat) False)[i := True], max i m, n + one_uint32_nat)
     })
  })\<close>

lemma length_list_grow[simp]:
  \<open>length (list_grow xs n a) = max (length xs) n\<close>
  by (auto simp: list_grow_def)

lemma list_update_append2: \<open>i \<ge> length xs \<Longrightarrow> (xs @ ys)[i := x] = xs @ ys[i - length xs := x]\<close>
  by (induction xs arbitrary: i) (auto split: nat.splits)

lemma lbd_ref_write_lbd_write:
  \<open>(uncurry (lbd_ref_write), uncurry (RETURN oo lbd_write)) \<in>
    [\<lambda>(lbd, i). i \<le> Suc (uint_max div 2)]\<^sub>f
     lbd_ref \<times>\<^sub>f nat_rel \<rightarrow> \<langle>lbd_ref\<rangle>nres_rel\<close>
  unfolding lbd_ref_write_def lbd_write_def
  by (intro frefI nres_relI)
    (auto simp: level_in_lbd_ref_def level_in_lbd_def lbd_ref_def list_grow_def
        nth_append uint_max_def length_filter_update_true list_update_append2
        length_filter_update_false
      intro!: ASSERT_leI le_trans[OF length_filter_le])

sepref_definition lbd_write_code
  is \<open>uncurry lbd_ref_write\<close>
  :: \<open>lbd_int_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a lbd_int_assn\<close>
  unfolding lbd_ref_write_def
  by sepref

lemma lbd_write_hnr_[sepref_fr_rules]:
  \<open>(uncurry lbd_write_code, uncurry (RETURN \<circ>\<circ> lbd_write))
    \<in> [\<lambda>(lbd, i). i \<le> Suc (uint_max div 2)]\<^sub>a
      lbd_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> lbd_assn\<close>
  using lbd_write_code.refine[FCOMP lbd_ref_write_lbd_write]
  unfolding lbd_assn_def .


paragraph \<open>Cleaning the marked levels\<close>

definition lbd_emtpy_inv :: \<open>nat \<Rightarrow> bool list \<times> nat \<Rightarrow> bool\<close> where
  \<open>lbd_emtpy_inv m = (\<lambda>(xs, i). i \<le> Suc m \<and> (\<forall>j < i. xs ! j = False) \<and>
    (\<forall>j > m. j < length xs \<longrightarrow> xs ! j = False))\<close>

definition lbd_empty_ref where
  \<open>lbd_empty_ref = (\<lambda>(xs, m, _). do {
    (xs, i) \<leftarrow>
       WHILE\<^sub>T\<^bsup>lbd_emtpy_inv m\<^esup>
         (\<lambda>(xs, i). i \<le> m)
         (\<lambda>(xs, i). do {
            ASSERT(i < length xs);
            ASSERT(i + one_uint32_nat < uint_max);
            RETURN (xs[i := False], i + one_uint32_nat)})
         (xs, zero_uint32_nat);
     RETURN (xs, zero_uint32_nat, zero_uint32_nat)
  })\<close>

definition lbd_empty where
   \<open>lbd_empty xs = RETURN (replicate (length xs) False)\<close>

lemma lbd_empty_ref:
  assumes \<open>((xs, m, n), xs) \<in> lbd_ref\<close>
  shows
    \<open>lbd_empty_ref (xs, m, n) \<le> \<Down> lbd_ref (RETURN (replicate (length xs) False))\<close>
proof -
  have m_xs: \<open>m \<le> length xs\<close> and [simp]: \<open>xs \<noteq> []\<close> and le_xs: \<open>length xs \<le> uint_max div 2 + 2\<close>
    using assms by (auto simp: lbd_ref_def)
  have [iff]: \<open>(\<forall>j. \<not> j < (b :: nat)) \<longleftrightarrow> b = 0\<close> for b
    by auto
  have init: \<open>lbd_emtpy_inv m (xs, zero_uint32_nat)\<close>
    using assms m_xs unfolding lbd_emtpy_inv_def
    by (auto simp: lbd_ref_def)
  have lbd_remove: \<open>lbd_emtpy_inv m
       (a[b := False], b + one_uint32_nat)\<close>
    if
      inv: \<open>lbd_emtpy_inv m s\<close> and
      \<open>case s of (ys, i) \<Rightarrow> length ys = length xs\<close> and
      cond: \<open>case s of (xs, i) \<Rightarrow> i \<le> m\<close> and
      s: \<open>s = (a, b)\<close> and
      [simp]: \<open>b < length a\<close>
    for s a b
  proof -
    have 1: \<open>a[b := False] ! j = False\<close> if \<open>j<b\<close> for j
      using inv that unfolding lbd_emtpy_inv_def s
      by auto
    have 2: \<open>\<forall>j>m. j < length (a[b := False]) \<longrightarrow> a[b := False] ! j = False\<close>
      using inv that unfolding lbd_emtpy_inv_def s
      by auto
    have \<open>b + one_uint32_nat \<le> Suc m\<close>
      using cond unfolding s by simp
    moreover have \<open>a[b := False] ! j = False\<close> if \<open>j<b + one_uint32_nat\<close> for j
      using 1[of j] that cond by (cases \<open>j = b\<close>) auto
    moreover have \<open>\<forall>j>m. j < length (a[b := False]) \<longrightarrow> a[b := False] ! j = False\<close>
      using 2 by auto
    ultimately show ?thesis
      unfolding lbd_emtpy_inv_def by auto
  qed
  have lbd_final: \<open>((a, zero_uint32_nat, zero_uint32_nat), replicate (length xs) False) \<in> lbd_ref\<close>
    if
      lbd: \<open>lbd_emtpy_inv m s\<close> and
      I': \<open>case s of (ys, i) \<Rightarrow> length ys = length xs\<close> and
      cond: \<open>\<not> (case s of (xs, i) \<Rightarrow> i \<le> m)\<close> and
      s: \<open>s = (a, b)\<close>
      for s a b
  proof -
    have 1: \<open>a[b := False] ! j = False\<close> if \<open>j<b\<close> for j
      using lbd that unfolding lbd_emtpy_inv_def s
      by auto
    have 2: \<open>j>m \<longrightarrow> j < length a \<longrightarrow> a ! j = False\<close> for j
      using lbd that unfolding lbd_emtpy_inv_def s
      by auto
    have [simp]: \<open>length a = length xs\<close>
      using I' unfolding s by auto
    have [simp]: \<open>b = Suc m\<close>
      using cond lbd unfolding lbd_emtpy_inv_def s
      by auto
    have [dest]: \<open>i < length xs \<Longrightarrow> \<not>a ! i\<close> for i
      using 1[of i] 2[of i] by (cases \<open>i < Suc m\<close>) auto

    have [simp]: \<open>a = replicate (length xs) False\<close>
      unfolding list_eq_iff_nth_eq
      apply (intro conjI)
      subgoal by simp
      subgoal by auto
      done
    show ?thesis
      using le_xs by (auto simp: lbd_ref_def)
  qed
  show ?thesis
    unfolding lbd_empty_ref_def conc_fun_RETURN
    apply clarify
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(xs, i). Suc m - i)\<close> and
      I' = \<open>\<lambda>(ys, i). length ys = length xs\<close>])
    subgoal by auto
    subgoal by (rule init)
    subgoal by auto
    subgoal using assms by (auto simp: lbd_ref_def)
    subgoal using m_xs le_xs by (auto simp: uint_max_def)
    subgoal by (rule lbd_remove)
    subgoal by auto
    subgoal by auto
    subgoal by (rule lbd_final)
    done
qed

lemma lbd_empty_ref_lbd_empty:
  \<open>(lbd_empty_ref, lbd_empty) \<in> lbd_ref \<rightarrow>\<^sub>f \<langle>lbd_ref\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for lbd m lbd'
    using lbd_empty_ref[of lbd m]
    by (auto simp: lbd_empty_def lbd_ref_def)
  done

sepref_definition lbd_empty_code
  is \<open>lbd_empty_ref\<close>
  :: \<open>lbd_int_assn\<^sup>d  \<rightarrow>\<^sub>a lbd_int_assn\<close>
  unfolding lbd_empty_ref_def
  by sepref

lemma lbd_empty_hnr[sepref_fr_rules]:
  \<open>(lbd_empty_code, lbd_empty) \<in> lbd_assn\<^sup>d \<rightarrow>\<^sub>a lbd_assn\<close>
  using lbd_empty_code.refine[FCOMP lbd_empty_ref_lbd_empty]
  unfolding lbd_assn_def .

definition (in -)empty_lbd :: \<open>lbd\<close> where
   \<open>empty_lbd = (replicate 32 False)\<close>

definition empty_lbd_ref :: \<open>lbd_ref\<close> where
   \<open>empty_lbd_ref = (replicate 32 False, zero_uint32_nat, zero_uint32_nat)\<close>

lemma empty_lbd_ref_empty_lbd:
  \<open>(uncurry0 (RETURN empty_lbd_ref), uncurry0 (RETURN empty_lbd)) \<in> unit_rel \<rightarrow>\<^sub>f \<langle>lbd_ref\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: empty_lbd_def lbd_ref_def empty_lbd_ref_def
      uint_max_def nth_Cons split: nat.splits)

sepref_definition empty_lbd_code
  is \<open>uncurry0 (RETURN empty_lbd_ref)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a lbd_int_assn\<close>
  unfolding empty_lbd_ref_def array_fold_custom_replicate
  by sepref

lemma empty_lbd_hnr[sepref_fr_rules]:
  \<open>(uncurry0 empty_lbd_code, uncurry0 (RETURN empty_lbd)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a lbd_assn\<close>
  using empty_lbd_code.refine[FCOMP empty_lbd_ref_empty_lbd]
  unfolding lbd_assn_def .


paragraph \<open>Extracting the LBD\<close>

text \<open>We do not prove correctness of our algorithm, as we don't care about the actual returned
value (for correctness).\<close>
definition get_LBD :: \<open>lbd \<Rightarrow> nat nres\<close> where
  \<open>get_LBD lbd = SPEC(\<lambda>_. True)\<close>

definition get_LBD_ref :: \<open>lbd_ref \<Rightarrow> nat nres\<close> where
  \<open>get_LBD_ref = (\<lambda>(xs, m, n). RETURN n)\<close>

lemma get_LBD_ref:
 \<open>((lbd, m), lbd') \<in> lbd_ref \<Longrightarrow> get_LBD_ref (lbd, m) \<le> \<Down> nat_rel (get_LBD lbd')\<close>
  unfolding get_LBD_ref_def get_LBD_def
  by (auto split:prod.splits)

lemma get_LBD_ref_get_LBD:
  \<open>(get_LBD_ref, get_LBD) \<in> lbd_ref \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for lbd m n lbd'
    using get_LBD_ref[of lbd]
    by (auto simp: lbd_empty_def lbd_ref_def)
  done


sepref_definition get_LBD_code
  is \<open>get_LBD_ref\<close>
  :: \<open>lbd_int_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding get_LBD_ref_def
  by sepref

lemma get_LBD_hnr[sepref_fr_rules]:
  \<open>(get_LBD_code, get_LBD) \<in> lbd_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  using get_LBD_code.refine[FCOMP get_LBD_ref_get_LBD, unfolded lbd_assn_def[symmetric]] .

end
