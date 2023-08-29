theory Heaps_Abs
  imports Ordered_Pairing_Heap_List2
    Weidenbach_Book_Base.Explorer
    Isabelle_LLVM.IICF
    More_Sepref.WB_More_Refinement
begin


text \<open>
  We first tried to follow the setup from Isabelle LLVM, but it is not
  clear how useful this really is. Hence we adapted the definition from
  the abstract operations.
\<close>
locale hmstruct_with_prio =
    fixes lt :: \<open>'v \<Rightarrow> 'v \<Rightarrow> bool\<close> and
    le :: \<open>'v \<Rightarrow> 'v \<Rightarrow> bool\<close>
  assumes hm_le: \<open>\<And>a b. le a b \<longleftrightarrow> a = b \<or> lt a b\<close> and
    hm_trans: \<open>transp le\<close> and
    hm_transt: \<open>transp lt\<close> and
    hm_totalt: \<open>totalp lt\<close>
begin

    definition prio_peek_min where
      "prio_peek_min \<equiv>  (\<lambda>(\<A>, b, w). (\<lambda>v.
          v \<in># b
        \<and> (\<forall>v'\<in>set_mset b. le (w v) (w v'))))"

    definition mop_prio_peek_min where
      "mop_prio_peek_min \<equiv>  (\<lambda>(\<A>, b, w). doN {ASSERT (b\<noteq>{#}); SPEC (prio_peek_min (\<A>, b,w))})"

    definition mop_prio_change_weight where
      "mop_prio_change_weight \<equiv>  (\<lambda>v \<omega> (\<A>, b, w). doN {
        ASSERT (v \<in># \<A>);
        ASSERT (v \<in># b \<longrightarrow> le \<omega> (w v));
        RETURN (\<A>, b, w(v := \<omega>))
     })"

    definition mop_prio_insert where
      "mop_prio_insert \<equiv>  (\<lambda>v \<omega> (\<A>, b, w). doN {
        ASSERT (v \<notin># b \<and>  v\<in>#\<A>);
        RETURN (\<A>, add_mset v b, w(v := \<omega>))
     })"

    definition mop_prio_is_in where
      \<open>mop_prio_is_in = (\<lambda>v (\<A>, b, w). do {
      ASSERT (v \<in># \<A>);
      RETURN (v \<in>#b)
      })\<close>
    definition mop_prio_insert_maybe where
      "mop_prio_insert_maybe \<equiv>  (\<lambda>v \<omega> (bw). doN {
        b \<leftarrow> mop_prio_is_in v bw;
        if \<not>b then mop_prio_insert v \<omega> (bw)
        else mop_prio_change_weight v \<omega> (bw)
     })"

     text \<open>TODO this is a shortcut and it could make sense to force w to remember the old values.\<close>
    definition mop_prio_old_weight where
      "mop_prio_old_weight = (\<lambda>v (\<A>, b, w). doN {
        ASSERT (v \<in># \<A>);
        b \<leftarrow> mop_prio_is_in v (\<A>, b, w);
        if b then RETURN (w v) else RES UNIV
     })"

    definition mop_prio_insert_raw_unchanged where
      "mop_prio_insert_raw_unchanged = (\<lambda>v h. doN {
        ASSERT (v \<notin># fst (snd h));
        w \<leftarrow> mop_prio_old_weight v h;
        mop_prio_insert v w h
     })"

    definition mop_prio_insert_unchanged where
      "mop_prio_insert_unchanged =  (\<lambda>v (bw). doN {
        b \<leftarrow> mop_prio_is_in v bw;
        if \<not>b then mop_prio_insert_raw_unchanged v (bw)
        else RETURN bw
     })"

    definition prio_del where
      \<open>prio_del = (\<lambda>v (\<A>, b, w). (\<A>, b - {#v#}, w))\<close>

    definition mop_prio_del where
      "mop_prio_del = (\<lambda>v (\<A>, b, w). doN {
        ASSERT (v \<in># b \<and> v \<in># \<A>);
        RETURN (prio_del v (\<A>, b, w))
     })"

    definition mop_prio_pop_min where
      "mop_prio_pop_min = (\<lambda>\<A>bw. doN {
      v \<leftarrow> mop_prio_peek_min \<A>bw;
      bw \<leftarrow> mop_prio_del v \<A>bw;
      RETURN (v, bw)
      })"

sublocale pairing_heap
  by unfold_locales (rule hm_le hm_trans hm_transt hm_totalt)+

end

end
