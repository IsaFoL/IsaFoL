theory IsaSAT_ACIDS
  imports IsaSAT_Literals
    Heaps_Abs
begin
text \<open>Instead of using VSIDS (which requires float), we use the more stable ACIDS variant
  that works simply on integers and does not seem much worse.

  We use ACIDS in a practical way, i.e., when the weight reaches the maximum
integer, we simply stop incrementing it. \<close>

(*TODO rename VSIDS to ACIDS even if the difference is simply the bumping score*)
section \<open>ACIDS\<close>

type_synonym ('a, 'v) acids = \<open>('a multiset \<times> ('a multiset \<times> ('a \<Rightarrow> 'v)) \<times> 'v)\<close>
definition acids :: \<open>'a multiset \<Rightarrow> ('a, 'ann) ann_lits \<Rightarrow> ('a, 'v::linorder) acids set\<close> where
\<open>acids \<A> M = {(\<B>, (b, w), m). \<B> = \<A> \<and> b \<subseteq># \<A> \<and> Max (w ` set_mset \<A>) \<le> m \<and> (\<forall>L \<in>#\<A>. L \<notin># b \<longrightarrow> defined_lit M (Pos L)) \<and> distinct_mset b}\<close>

lemma acids_prepend: \<open>ac \<in> acids \<A> M \<Longrightarrow> ac \<in> acids \<A> (L # M)\<close>
  unfolding acids_def by (auto simp: defined_lit_map)

interpretation ACIDS: hmstruct_with_prio where
  le = \<open>(\<ge>) :: nat \<Rightarrow> nat \<Rightarrow> bool\<close> and
  lt = \<open>(>)\<close>
  apply unfold_locales
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: transp_def)
  subgoal by (auto simp: totalp_on_def)
  done

definition acids_tl :: \<open>'a \<Rightarrow> ('a, 'v) acids \<Rightarrow> ('a, 'v) acids nres\<close> where
  \<open>acids_tl L = (\<lambda>(\<B>, ac, m). do {
    ASSERT (L \<in># \<B>);
    ac \<leftarrow> ACIDS.mop_prio_insert_unchanged L ac;
    RETURN (\<B>, ac, m)
  })\<close>

lemma acids_tl:
  \<open>ac \<in> acids \<A> M \<Longrightarrow> L \<in># \<A> \<Longrightarrow> M \<noteq> [] \<Longrightarrow> L = atm_of (lit_of (hd M)) \<Longrightarrow> acids_tl L ac \<le> RES (acids \<A> (tl M))\<close>
  unfolding acids_tl_def ACIDS.mop_prio_insert_unchanged_def
    ACIDS.mop_prio_insert_raw_unchanged_def
  apply refine_vcg
  subgoal
    by (cases M) (auto simp: acids_def ACIDS.mop_prio_insert_unchanged_def insert_subset_eq_iff
      intro!: subset_add_mset_notin_subset)
  subgoal
    apply (cases M)
    apply (auto simp: acids_def ACIDS.mop_prio_insert_unchanged_def
      defined_lit_map)
    using insert_subset_eq_iff subset_add_mset_notin_subset by fastforce
  done

definition acids_get_min :: \<open>('a, nat) acids \<Rightarrow> 'a nres\<close> where
  \<open>acids_get_min = (\<lambda>(\<B>, ac, m). do {
    L \<leftarrow> ACIDS.mop_prio_peek_min ac;
    RETURN L
  })\<close>

definition acids_mset where
  \<open>acids_mset x = fst (fst (snd x))\<close>

lemma acids_get_min:
  \<open>acids_mset x \<noteq> {#} \<Longrightarrow> acids_get_min x \<le> SPEC (\<lambda>v. ACIDS.prio_peek_min (fst (snd x)) v)\<close>
  unfolding acids_get_min_def ACIDS.mop_prio_peek_min_def acids_mset_def
  by refine_vcg (auto simp: ACIDS.prio_peek_min_def)

definition acids_pop_min :: \<open>('a, nat) acids \<Rightarrow> ('a \<times> ('a, nat) acids) nres\<close> where
  \<open>acids_pop_min = (\<lambda>(\<B>, ac, m). do {
    (v, ac) \<leftarrow> ACIDS.mop_prio_pop_min ac;
    RETURN (v, (\<B>, ac, m))
  })\<close>

definition acids_find_next_undef :: \<open>nat multiset \<Rightarrow> (nat, nat) acids \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat option \<times> (nat, nat) acids) nres\<close> where
\<open>acids_find_next_undef \<A> = (\<lambda>ac M. do {
  WHILE\<^sub>T\<^bsup>(\<lambda>(L, ac).
        (L = None \<longrightarrow> ac \<in> acids \<A> M) \<and>
        (L \<noteq> None \<longrightarrow> ac \<in> acids \<A> (Decided (Pos (the L)) # M) \<and> Pos (the L) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> undefined_lit M (Pos (the L))))
  \<^esup>
      (\<lambda>(nxt, ac). nxt = None \<and> acids_mset ac \<noteq> {#})
      (\<lambda>(a, ac). do {
         ASSERT (a = None);
         (L, ac) \<leftarrow> acids_pop_min ac;
         ASSERT(Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l  \<A>);
         if defined_lit M (Pos L) then RETURN (None, ac)
         else RETURN (Some L, ac)
        }
      )
      (None, ac)
  })\<close>

lemma acids_pop_min:
  \<open>acids_mset x \<noteq> {#} \<Longrightarrow> x \<in> acids \<A> M \<Longrightarrow>
  acids_pop_min x \<le> SPEC (\<lambda>(v, ac). acids_mset ac = acids_mset x - {#v#} \<and> v \<in># acids_mset x \<and>
    ACIDS.prio_peek_min (fst (snd x)) v \<and>
    (defined_lit M (Pos v) \<longrightarrow> ac \<in> acids \<A> M) \<and>
    (undefined_lit M (Pos v) \<longrightarrow> ac \<in> acids \<A> (Decided (Pos v) # M)))\<close>
  unfolding ACIDS.mop_prio_pop_min_def acids_pop_min_def
    ACIDS.mop_prio_peek_min_def ACIDS.mop_prio_del_def
  by refine_vcg
   (auto simp: acids_def ACIDS.prio_peek_min_def distinct_mset_remove1_All ACIDS.prio_del_def
      defined_lit_map acids_mset_def dest: in_diffD)

lemma acids_find_next_undef:
  assumes
    vmtf: \<open>ac \<in> acids \<A> M\<close>
  shows \<open>acids_find_next_undef \<A> ac M
     \<le> \<Down> Id (SPEC (\<lambda>(L, ac).
        (L = None \<longrightarrow> ac \<in> acids \<A> M \<and> (\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l \<A>. defined_lit M L)) \<and>
        (L \<noteq> None \<longrightarrow> ac \<in> acids \<A> (Decided (Pos (the L)) # M) \<and> Pos (the L) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> undefined_lit M (Pos (the L)))))\<close>
proof -
  have [refine0]: \<open>wf (measure (\<lambda>(_, ac). size (acids_mset ac)))\<close>
    by auto
  show ?thesis
    unfolding acids_find_next_undef_def
    apply (refine_vcg acids_pop_min[of _ \<A> M, THEN order_trans])
    subgoal using assms by auto
    subgoal by auto
    subgoal by (auto simp: ACIDS.prio_peek_min_def acids_def acids_mset_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: acids_def ACIDS.prio_peek_min_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: ACIDS.prio_peek_min_def acids_mset_def dest: multi_member_split)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: ACIDS.prio_peek_min_def acids_mset_def dest: multi_member_split)
    subgoal by auto
    subgoal by (auto simp: ACIDS.prio_peek_min_def acids_mset_def acids_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n dest!: multi_member_split[of \<open>_ :: nat\<close>])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

end
