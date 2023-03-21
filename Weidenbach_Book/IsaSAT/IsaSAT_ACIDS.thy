theory IsaSAT_ACIDS
  imports IsaSAT_Literals
    IsaSAT_VSIDS
    Pairing_Heaps
begin
text \<open>Instead of using VSIDS (which requires float), we use the more stable ACIDS variant
  that works simply on integers and does not seem much worse.

  We use ACIDS in a practical way, i.e., when the weight reaches the maximum
integer, we simply stop incrementing it. \<close>

(*TODO rename VSIDS to ACIDS even if the difference is simply the bumping score*)
section \<open>ACIDS\<close>

definition acids :: \<open>'a multiset \<Rightarrow> ('a, 'ann) ann_lits \<Rightarrow> 'a multiset \<times> ('a \<Rightarrow> 'v) \<times> 'v :: linorder \<Rightarrow> bool\<close> where
\<open>acids \<A> M = (\<lambda>(b, w, m). b \<subseteq># \<A> \<and> Max (w ` set_mset \<A>) \<le> m \<and> (\<forall>L \<in>#\<A>. L \<notin># b \<longrightarrow> defined_lit M (Pos L)))\<close>
thm VSIDS.mop_prio_peek_min_def
end
