theory Propo_DPLL_Implementation
imports Propo_DPLL
begin

datatype ('state, 'b) propagated = Step "'state" | Conflicting "'state" | Unit

locale two_watched_literals =
  fixes get_clauses :: "nat literal \<Rightarrow> 'state \<Rightarrow> 'b list" and
  get_watched :: "'b \<Rightarrow> 'state \<Rightarrow> nat literal list" and
  get_not_watched :: "'b \<Rightarrow> 'state \<Rightarrow> nat literal list" and
  update_st :: "'b \<Rightarrow> 'state \<Rightarrow> nat literal \<Rightarrow> ('state, 'b) propagated" and
  get_clause :: "'b \<Rightarrow> 'state \<Rightarrow> nat clause" and
  trail :: "'state \<Rightarrow> nat dpll_annoted_lits" and
  clauses :: "'state \<Rightarrow> nat clauses"
  assumes get_watched:
    "\<And>L q st. q\<in> set (get_clauses L st) \<Longrightarrow> -L \<in> set (get_watched q st)" and
  two_watched_lit:
    "\<And>L q st.  q\<in> set (get_clauses L st) \<Longrightarrow> \<exists>a b. get_watched q st = [a, b]" and
  watched_not_watched_is_clause:
    "\<And>L q st. q\<in> set (get_clauses L st)
      \<Longrightarrow> mset (get_watched q st @ get_not_watched q st) = get_clause q st" and
  update_st:
    "\<And>\<phi> L st \<psi> st'. \<phi> \<in> set (get_clauses L st) \<Longrightarrow> \<phi> \<noteq> \<psi> \<Longrightarrow> update_st \<psi> st L = Step st'
      \<Longrightarrow> \<phi> \<in> set (get_clauses L st')" and
  watched_lits_are_true:
    "\<And>L q st a.  q\<in> set (get_clauses L st) \<Longrightarrow> a\<in>set (get_watched q ts)
      \<Longrightarrow> undefined_lit a (trail st)" and
  update_unit:
    "\<And>\<phi> st L. update_st \<phi> st L = Unit
      \<longleftrightarrow> trail st \<Turnstile>as CNot (mset (get_not_watched \<phi> st))"
begin
  fun get_unit_lit where
  "get_unit_lit [a, b] L = (if L = a then b else a)"

  fun propagate1 where
  "propagate1 L [] st = (st, [])" |
  "propagate1 L (\<phi> # \<phi>s) st =
    (case update_st \<phi> st L of
      Step st' \<Rightarrow> propagate1 L \<phi>s st'
    | Conflicting st' \<Rightarrow> (st', [])
    | Unit \<Rightarrow>
      let (st', Ls) = propagate1 L \<phi>s st in
      (st', get_unit_lit (get_watched \<phi> st) L # Ls))"


  lemma "distinct \<phi>s \<Longrightarrow> \<phi> : set \<phi>s \<Longrightarrow> \<phi>' \<in> set \<phi>s \<Longrightarrow> \<phi> \<noteq> \<phi>' \<Longrightarrow> update_st \<phi> st L = Step st' \<Longrightarrow> update_st \<phi>' st = update_st \<phi> st'"
  oops
  lemma
    "update_st \<phi> st L = Step st' \<Longrightarrow> snd (propagate1 L \<phi>s st) = snd (propagate1 L \<phi>s st')"
    apply (induction \<phi>s arbitrary: )
    apply auto
    (**)
    oops




  lemma
    assumes
      "\<forall>\<phi>\<in>set \<phi>s. \<phi> \<in> set (get_clauses P st)" and
      "l \<in> set (snd (propagate1 L \<phi>s st))"
    shows "\<exists>C L. C + {#L#} \<in> clauses st \<and> trail st \<Turnstile>as CNot C \<and> undefined_lit L (trail st)"
    using assms
proof (induction \<phi>s arbitrary: st)
  case Nil thus ?case by simp
next
  case (Cons \<phi> \<phi>s) note IH = this(1) and \<phi>=this(2) and l = this(3)
  show ?case
    proof (cases "update_st \<phi> st L")
      case (Conflicting st')
      thus ?thesis using Cons(3) by auto
    next
      case (Step st')
      thus ?thesis using IH[of st] \<phi> l by auto
end
end
