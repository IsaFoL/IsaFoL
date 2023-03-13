theory IsaSAT_Bump_Heuristics_State
imports Watched_Literals_VMTF
  IsaSAT_VSIDS
  Tuple4
begin

(*TODO: share the to_remove part of Bump_Heuristics*)
type_synonym bump_heuristics = \<open>(vmtf_remove_int, vmtf_remove_int, bool, nat) tuple4\<close>

abbreviation Bump_Heuristics :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bump_heuristics\<close> where
  \<open>Bump_Heuristics a b c d \<equiv> Tuple4 a b c d\<close>

lemmas bump_heuristics_splits = Tuple4.tuple4.splits
hide_fact tuple4.splits

abbreviation get_stable_heuristics :: \<open>bump_heuristics \<Rightarrow> vmtf_remove_int\<close> where
  \<open>get_stable_heuristics \<equiv> Tuple4_a\<close>

abbreviation get_focused_heuristics :: \<open>bump_heuristics \<Rightarrow> vmtf_remove_int\<close> where
  \<open>get_focused_heuristics \<equiv> Tuple4_b\<close>

abbreviation is_focused_heuristics :: \<open>bump_heuristics \<Rightarrow> bool\<close> where
  \<open>is_focused_heuristics \<equiv> Tuple4_c\<close>

abbreviation conflict_count :: \<open>bump_heuristics \<Rightarrow> nat\<close> where
  \<open>conflict_count \<equiv> Tuple4_d\<close>

abbreviation set_stable_heuristics :: \<open>vmtf_remove_int \<Rightarrow>bump_heuristics \<Rightarrow> _\<close> where
  \<open>set_stable_heuristics \<equiv> Tuple4.set_a\<close>

abbreviation set_focused_heuristics :: \<open>vmtf_remove_int \<Rightarrow>bump_heuristics \<Rightarrow> _\<close> where
  \<open>set_focused_heuristics \<equiv> Tuple4.set_b\<close>

abbreviation set_is_focused_heuristics :: \<open>bool \<Rightarrow>bump_heuristics \<Rightarrow> _\<close> where
  \<open>set_is_focused_heuristics \<equiv> Tuple4.set_c\<close>

abbreviation set_conflict_count :: \<open>nat \<Rightarrow>bump_heuristics \<Rightarrow> _\<close> where
  \<open>set_conflict_count \<equiv> Tuple4.set_d\<close>

definition bump_heur :: \<open>_ \<Rightarrow> _ \<Rightarrow> bump_heuristics set\<close> where
  \<open>bump_heur \<A> M = {x.
    is_focused_heuristics x \<longrightarrow>
      (get_stable_heuristics x \<in> vmtf \<A> M \<and>
      get_focused_heuristics x \<in> vmtf \<A> (takeWhile (\<lambda>x. \<not>is_decided x) M)) \<and>
    \<not>is_focused_heuristics x \<longrightarrow>
      (get_stable_heuristics x \<in> vmtf \<A> (takeWhile (\<lambda>x. \<not>is_decided x) M) \<and>
      get_focused_heuristics x \<in> vmtf \<A> M)}\<close>

definition switch_bump_heur :: \<open>bump_heuristics \<Rightarrow> bump_heuristics\<close> where
  \<open>switch_bump_heur x = do {
    (set_is_focused_heuristics (\<not>(is_focused_heuristics x)) x)
  }\<close>

lemma switch_bump_heur:
  assumes \<open>x \<in> bump_heur \<A> M\<close> and
    \<open>count_decided M = 0\<close>
  shows \<open>switch_bump_heur x \<in> bump_heur \<A> M\<close>
  using assms
  by (cases x)
   (auto simp: switch_bump_heur_def bump_heur_def)


subsection \<open>Access Function\<close>
definition isa_vmtf_unset :: \<open>nat \<Rightarrow> bump_heuristics \<Rightarrow> bump_heuristics\<close> where
  \<open>isa_vmtf_unset L vm = (case vm of Tuple4 (hstable) (focused) foc a \<Rightarrow>
  Tuple4 (if \<not>foc then vmtf_unset L hstable else hstable)
    (if foc then vmtf_unset L focused else focused)
    foc a)\<close>

lemma isa_vmtf_consD:
  \<open>x \<in> bump_heur \<A> M \<Longrightarrow> x \<in> bump_heur \<A> (L # M)\<close>
  by (auto simp: bump_heur_def dest: vmtf_consD)


lemma isa_vmtf_unset_vmtf_tl:
  fixes M
  defines [simp]: \<open>L \<equiv> atm_of (lit_of (hd M))\<close>
  assumes vmtf:\<open>x\<in> bump_heur \<A> M\<close> and
    L_N: \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> and [simp]: \<open>M \<noteq> []\<close>
  shows \<open>isa_vmtf_unset L x \<in> bump_heur \<A> (tl M)\<close>
proof -
  obtain ns m fst_As lst_As next_search remove where
    \<open>is_focused_heuristics x \<Longrightarrow> get_focused_heuristics x = ((ns, m, fst_As, lst_As, next_search), remove)\<close>
    \<open>\<not>is_focused_heuristics x \<Longrightarrow> get_stable_heuristics x = ((ns, m, fst_As, lst_As, next_search), remove)\<close>
   by (cases \<open>get_focused_heuristics x\<close>; cases \<open>get_stable_heuristics x\<close>; cases \<open>is_focused_heuristics x\<close>) auto
  show ?thesis
    using vmtf_unset_vmtf_tl[of ns m fst_As lst_As next_search remove \<A> M]
      assms by (auto simp: bump_heur_def)
qed

end