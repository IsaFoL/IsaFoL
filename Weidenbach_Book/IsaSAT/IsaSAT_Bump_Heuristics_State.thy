theory IsaSAT_Bump_Heuristics_State
  imports Watched_Literals_VMTF
    IsaSAT_ACIDS
  Tuple4
begin

(*TODO: share the to_remove part of Bump_Heuristics*)
type_synonym bump_heuristics = \<open>((nat, nat) acids, vmtf, bool, nat list \<times> bool list) tuple4\<close>

abbreviation Bump_Heuristics :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bump_heuristics\<close> where
  \<open>Bump_Heuristics a b c d \<equiv> Tuple4 a b c d\<close>

lemmas bump_heuristics_splits = Tuple4.tuple4.splits
hide_fact tuple4.splits

abbreviation get_stable_heuristics :: \<open>bump_heuristics \<Rightarrow> (nat, nat) acids\<close> where
  \<open>get_stable_heuristics \<equiv> Tuple4_a\<close>

abbreviation get_focused_heuristics :: \<open>bump_heuristics \<Rightarrow> vmtf\<close> where
  \<open>get_focused_heuristics \<equiv> Tuple4_b\<close>

abbreviation is_focused_heuristics :: \<open>bump_heuristics \<Rightarrow> bool\<close> where
  \<open>is_focused_heuristics \<equiv> Tuple4_c\<close>

abbreviation is_stable_heuristics:: \<open>bump_heuristics \<Rightarrow> bool\<close> where
  \<open>is_stable_heuristics x \<equiv> \<not>is_focused_heuristics x\<close>

abbreviation get_bumped_variables :: \<open>bump_heuristics \<Rightarrow> nat list \<times> bool list\<close> where
  \<open>get_bumped_variables \<equiv> Tuple4_d\<close>

abbreviation set_stable_heuristics :: \<open>(nat, nat) acids \<Rightarrow>bump_heuristics \<Rightarrow> _\<close> where
  \<open>set_stable_heuristics \<equiv> Tuple4.set_a\<close>

abbreviation set_focused_heuristics :: \<open>vmtf \<Rightarrow>bump_heuristics \<Rightarrow> _\<close> where
  \<open>set_focused_heuristics \<equiv> Tuple4.set_b\<close>

abbreviation set_is_focused_heuristics :: \<open>bool \<Rightarrow>bump_heuristics \<Rightarrow> _\<close> where
  \<open>set_is_focused_heuristics \<equiv> Tuple4.set_c\<close>

abbreviation set_bumped_variables :: \<open>nat list \<times> bool list \<Rightarrow>bump_heuristics \<Rightarrow> _\<close> where
  \<open>set_bumped_variables \<equiv> Tuple4.set_d\<close>

definition get_unit_trail where
  \<open>get_unit_trail M = (rev (takeWhile (\<lambda>x. \<not>is_decided x) (rev M)))\<close>

definition bump_heur :: \<open>_ \<Rightarrow> _ \<Rightarrow> bump_heuristics set\<close> where
  \<open>bump_heur \<A> M = {x.
    (is_focused_heuristics x \<longrightarrow>
      (get_stable_heuristics x \<in> acids \<A> (get_unit_trail M)  \<and>
      get_focused_heuristics x \<in> vmtf \<A> M)) \<and>
    (\<not>is_focused_heuristics x \<longrightarrow>
      (get_stable_heuristics x \<in> acids \<A> M \<and>
       get_focused_heuristics x \<in> vmtf \<A> (get_unit_trail M))) \<and>
   (get_bumped_variables x, set (fst (get_bumped_variables x))) \<in> distinct_atoms_rel \<A>
  }\<close>

definition switch_bump_heur :: \<open>bump_heuristics \<Rightarrow> bump_heuristics\<close> where
  \<open>switch_bump_heur x = do {
    (set_is_focused_heuristics (\<not>(is_focused_heuristics x)) x)
  }\<close>

lemma get_unit_trail_count_decided_0[simp]: \<open>count_decided M = 0 \<Longrightarrow> get_unit_trail M = M\<close>
  by (auto simp: get_unit_trail_def count_decided_0_iff)
   (metis rev_swap set_rev takeWhile_eq_all_conv)

lemma switch_bump_heur:
  assumes \<open>x \<in> bump_heur \<A> M\<close> and
    \<open>count_decided M = 0\<close>
  shows \<open>switch_bump_heur x \<in> bump_heur \<A> M\<close>
  using assms
  by (cases x)
   (auto simp: switch_bump_heur_def bump_heur_def)


subsection \<open>Access Function\<close>
definition isa_bump_unset_pre where
  \<open>isa_bump_unset_pre = (\<lambda>L x.
  (is_focused_heuristics x \<longrightarrow> vmtf_unset_pre L (get_focused_heuristics x)) \<and>
  (is_stable_heuristics x \<longrightarrow> acids_tl_pre L (get_stable_heuristics x))
  )\<close>
definition isa_bump_unset :: \<open>nat \<Rightarrow> bump_heuristics \<Rightarrow> bump_heuristics nres\<close> where
  \<open>isa_bump_unset L vm = (case vm of Tuple4 (hstable) (focused) foc a \<Rightarrow> do {
  hstable \<leftarrow> (if \<not>foc then acids_tl L hstable else RETURN hstable);
  let focused = (if foc then vmtf_unset L focused else focused);
  RETURN (Tuple4 hstable focused foc a)
  })\<close>

lemma get_unit_trail_simps[simp]: \<open>is_decided L \<Longrightarrow> get_unit_trail (L # M) = get_unit_trail M\<close>
  \<open>\<not>is_decided L \<Longrightarrow> count_decided M = 0 \<Longrightarrow> get_unit_trail (L # M) = L # M\<close>
  \<open>\<not>is_decided L \<Longrightarrow> count_decided M > 0 \<Longrightarrow> get_unit_trail (L # M) = get_unit_trail M\<close>
  apply (auto simp: get_unit_trail_def takeWhile_append)
  apply (metis set_rev takeWhile_eq_all_conv)
  apply (metis count_decided_0_iff nat_neq_iff)
  using bot_nat_0.not_eq_extremum count_decided_0_iff by blast

lemma get_unit_trail_cons_if:
  \<open>get_unit_trail (L # M) = (if is_decided L then get_unit_trail M else if count_decided M = 0 then L # M else get_unit_trail M)\<close>
  by (auto simp: takeWhile_append)

lemma get_unit_trail_tl[simp]: \<open>count_decided M > 0 \<Longrightarrow> get_unit_trail (tl M) = get_unit_trail M\<close>
  by (cases M; cases \<open>hd M\<close>) auto

lemma isa_vmtf_consD:
  \<open>x \<in> bump_heur \<A> M \<Longrightarrow> x \<in> bump_heur \<A> (L # M)\<close>
  by (auto simp add: bump_heur_def takeWhile_append get_unit_trail_cons_if
      intro!: vmtf_consD' acids_prepend)


lemma isa_bump_unset_vmtf_tl:
  fixes M
  defines [simp]: \<open>L \<equiv> atm_of (lit_of (hd M))\<close>
  assumes vmtf: \<open>x\<in> bump_heur \<A> M\<close> and
    L_N: \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> and [simp]: \<open>M \<noteq> []\<close> and
    nz: \<open>count_decided M > 0\<close>
  shows \<open>isa_bump_unset L x \<le> SPEC (\<lambda>a. a \<in> bump_heur \<A> (tl M))\<close>
proof -
  obtain ns m fst_As lst_As next_search where
    \<open>is_focused_heuristics x \<Longrightarrow> get_focused_heuristics x = ((ns, m, fst_As, lst_As, next_search))\<close>
   by (cases \<open>get_focused_heuristics x\<close>; cases \<open>is_focused_heuristics x\<close>) auto
  then show ?thesis
    using vmtf_unset_vmtf_tl[of ns m fst_As lst_As next_search \<A> M] nz
      assms unfolding isa_bump_unset_def apply (cases x, simp only: tuple4.case Let_def)
    apply (cases \<open>is_focused_heuristics x\<close>)
    subgoal
      by (refine_vcg acids_tl[of _ \<A> M, THEN order_trans])
       (auto simp: bump_heur_def isa_bump_unset_def split: bump_heuristics_splits)
    subgoal
      by (refine_vcg acids_tl[of _ \<A> M, THEN order_trans])
        (auto simp: bump_heur_def isa_bump_unset_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n split: bump_heuristics_splits)
    done
qed


  (*TODO: this should probably be only the focused version, but for our first porting experiments, let's
  implement the switching version*)
definition bump_get_heuristics :: \<open>_ \<Rightarrow> vmtf\<close> where
  \<open>bump_get_heuristics x = (get_focused_heuristics x)\<close>

definition length_bumped_vmtf_array :: \<open>bump_heuristics \<Rightarrow> nat\<close> where
  \<open>length_bumped_vmtf_array x =
  length (fst (bump_get_heuristics x))\<close>

definition current_vmtf_array_nxt_score :: \<open>bump_heuristics \<Rightarrow> nat\<close> where
  \<open>current_vmtf_array_nxt_score x = fst (snd (bump_get_heuristics x))\<close>
definition access_focused_vmtf_array where
  \<open>access_focused_vmtf_array x i = do {
  ASSERT (i < length (fst (bump_get_heuristics x)));
  RETURN (fst (bump_get_heuristics x) ! i)}\<close>

definition bumped_vmtf_array_fst where
  \<open>bumped_vmtf_array_fst x =
  fst (snd (snd (bump_get_heuristics x)))\<close>

definition isa_bump_mark_to_rescore
  :: \<open>nat \<Rightarrow> bump_heuristics \<Rightarrow> bump_heuristics nres\<close>
where
  \<open>isa_bump_mark_to_rescore L x = (case x of Bump_Heuristics a b c d \<Rightarrow> do {
    ASSERT (atms_hash_insert_pre L d);
    RETURN (Bump_Heuristics a b c (atoms_hash_insert L d))
  })\<close>


end
