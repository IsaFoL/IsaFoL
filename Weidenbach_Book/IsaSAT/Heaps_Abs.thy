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
  assumes le: \<open>\<And>a b. le a b \<longleftrightarrow> a = b \<or> lt a b\<close> and
    trans: \<open>transp le\<close> and
    transt: \<open>transp lt\<close> and
    totalt: \<open>totalp lt\<close>
begin

    definition mop_prio_pop_min where
      "mop_prio_pop_min = (\<lambda>(b, w). doN {ASSERT (b\<noteq>{#}); SPEC (\<lambda>(v, (b', w)).
        v \<in># b
      \<and> b'=b - {#v#}
      \<and> (\<forall>v'\<in>set_mset b. le (w v) (w v')))})"

    definition mop_prio_peek_min where
      "mop_prio_peek_min \<equiv>  (\<lambda>(b, w). doN {ASSERT (b\<noteq>{#}); SPEC (\<lambda>v.
          v \<in># b
        \<and> (\<forall>v'\<in>set_mset b. le (w v) (w v')))})"

    definition mop_prio_change_weight where
      "mop_prio_change_weight \<equiv>  (\<lambda>v \<omega> (b, w). doN {
        if v \<in># b then RETURN (b,w)
        else RETURN (b, w(v := \<omega>))
     })"

    definition mop_prio_insert where
      "mop_prio_insert \<equiv>  (\<lambda>v \<omega> (b, w). doN {
        ASSERT (v \<notin># b);
        RETURN (add_mset v b, w(v := \<omega>))
     })"

    definition mop_prio_insert_maybe where
      "mop_prio_insert_maybe \<equiv>  (\<lambda>v \<omega> (bw). doN {
        if v \<notin># fst bw then mop_prio_insert v \<omega> (bw)
        else mop_prio_change_weight v \<omega> (bw)
     })"

sublocale pairing_heap
  by unfold_locales (rule le trans transt totalt)+

end

end
