theory CDCL_CW
imports Partial_Annotated_Clausal_Logic List_More CDCL_CW_Level Transition

begin
sledgehammer_params[verbose, e spass cvc4 z3 verit]
declare upt.simps(2)[simp del]

datatype 'a conflicting_clause = C_True | C_Clause "'a"

locale cw_state =
  fixes
    trail :: "'st::equal \<Rightarrow> ('v, 'lvl, 'mark) annoted_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow>'v clause conflicting_clause" and

    update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_init_clss :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_learned_clss :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause conflicting_clause \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" and
    mark_of_cls :: "'v clause \<Rightarrow> 'mark" and
    cls_of_mark :: "'mark \<Rightarrow> 'v clause" and
    restart_state :: "'st \<Rightarrow> 'st"
  assumes
    trail_update_trail[simp]: "\<And>M st. trail (update_trail M st) = M" and
    update_trail_update_clss[simp]: "\<And>st C. trail (update_init_clss C st) = trail st" and
    trail_update_learned[simp]: "\<And>C st. trail (update_learned_clss C st) = trail st" and
    trail_update_backtrack_lvl[simp]: "\<And>st C. trail (update_backtrack_lvl C st) = trail st" and
    trail_update_conflicting[simp]: "\<And>C st. trail (update_conflicting C st) = trail st" and

    trail_update_clss[simp]: "\<And>M st. init_clss (update_trail M st) = init_clss st" and
    init_clss_update_clss[simp]:
      "\<And>st C. init_clss (update_init_clss C st) = C" and
    init_clss_update_learned[simp]:
      "\<And>C st. init_clss (update_learned_clss C st) = init_clss st" and
    init_clss_update_backtrack_lvl[simp]:
      "\<And>st C. init_clss (update_backtrack_lvl C st) = init_clss st" and
    init_clss_update_conflicting[simp]:
      "\<And>C st. init_clss (update_conflicting C st) = init_clss st" and

    learned_update_trail[simp]: "\<And>M st. learned_clss (update_trail M st) = learned_clss st" and
    learned_update_clss[simp]: "\<And>st C. learned_clss (update_init_clss C st) = learned_clss st" and
    learned_update_learned[simp]: "\<And>C st. learned_clss (update_learned_clss C st) = C" and
    learned_update_backtrack_lvl[simp]:
      "\<And>st C. learned_clss (update_backtrack_lvl C st) = learned_clss st" and
    learned_update_conflicting[simp]:
      "\<And>C st. learned_clss (update_conflicting C st) = learned_clss st" and

    backtrack_lvl_update_trail[simp]:
      "\<And>M st. backtrack_lvl (update_trail M st) = backtrack_lvl st" and
    backtrack_lvl_update_init_clss[simp]:
      "\<And>st C. backtrack_lvl (update_init_clss C st) = backtrack_lvl st"  and
    backtrack_lvl_update_learned[simp]:
      "\<And>C st. backtrack_lvl (update_learned_clss C st) = backtrack_lvl st" and
    backtrack_lvl_update_backtrack_lvl[simp]:
      "\<And>st k. backtrack_lvl (update_backtrack_lvl k st) = k" and
    backtrack_lvl_update_conflicting[simp]:
      "\<And>C st. backtrack_lvl (update_conflicting C st) = backtrack_lvl st" and

    conflicting_update_trail[simp]:
      "\<And>M st. conflicting (update_trail M st) = conflicting st" and
    conflicting_update_init_clss[simp]:
      "\<And>st C. conflicting (update_init_clss C st) = conflicting st" and
    conflicting_update_learned[simp]:
      "\<And>C st. conflicting (update_learned_clss C st) = conflicting st" and
    conflicting_update_backtrack_lvl[simp]:
      "\<And>st C. conflicting (update_backtrack_lvl C st) = conflicting st" and
    conflicting_update_conflicting[simp]:
      "\<And>C st. conflicting (update_conflicting C st) = C" and

    init_state_trail[simp]: "\<And>N. finite N \<Longrightarrow> trail (init_state N) = []" and
    init_state_clss[simp]: "\<And>N. finite N \<Longrightarrow> init_clss (init_state N) = N" and
    init_state_learned_clss[simp]: "\<And>N. finite N \<Longrightarrow> learned_clss (init_state N) = {}" and
    init_state_backtrack_lvl[simp]: "\<And>N. finite N \<Longrightarrow> backtrack_lvl (init_state N) = 0" and
    init_state_conflicting[simp]: "\<And>N. finite N \<Longrightarrow> conflicting (init_state N) = C_True" and

    cls_of_mark_mark_of_cls[simp]: "\<And>C::'v clause. cls_of_mark (mark_of_cls C) = C" and
    mark_of_cls_cls_or_mark[simp]: "\<And>C::'mark. mark_of_cls (cls_of_mark C) = C" and


    st_equal: "\<And>S T. S = T
      \<longleftrightarrow> (trail S, init_clss S, learned_clss S, backtrack_lvl S, conflicting S)
          = (trail T, init_clss T, learned_clss T, backtrack_lvl T, conflicting T)" and
    trail_restart_state[simp]: "trail (restart_state S) = []" and
    init_clss_restart_state[simp]: "init_clss (restart_state S) = init_clss S" and
    learned_clss_restart_state[simp]: "learned_clss (restart_state S) = learned_clss S" and
    backtrack_lvl_restart_state[simp]: "backtrack_lvl (restart_state S) = 0" and
    conflicting_restart_state[simp]: "conflicting (restart_state S) = C_True"
begin

fun cons_trail where
"cons_trail (Propagated L m) S = update_trail (Propagated L (mark_of_cls m) # trail S) S"|
"cons_trail (Marked L m) S = update_trail (Marked L m # trail S) S"

abbreviation tl_trail :: "'st \<Rightarrow> 'st" where
"tl_trail S \<equiv> update_trail (tl (trail S)) S"

definition add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" where
"add_cls C S = update_learned_clss (insert C (learned_clss S)) S"

definition remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" where
"remove_cls C S =
  update_learned_clss (learned_clss S - {C}) (update_init_clss (init_clss S - {C}) S)"

lemma
  shows
    trail_add_cls[simp]: "trail (add_cls C S) = trail S" and
    init_clss_add_clause[simp]: "init_clss (add_cls C st) = init_clss st" and
    learned_clss_add_cls[simp]: "learned_clss (add_cls C S) = learned_clss S \<union> {C}" and
    backtrack_lvl_add_cls[simp]: "backtrack_lvl (add_cls C S) = backtrack_lvl S" and
    conflicting_add_cls[simp]: "conflicting (add_cls C S) = conflicting S"
  unfolding add_cls_def remove_cls_def by auto

lemma
  shows
    trail_remove_cls[simp]: "trail (remove_cls C S) = trail S" and
    init_clss_remove_clause[simp]: "init_clss (remove_cls C st) = init_clss st - {C}" and
    learned_clss_remove_cls[simp]: "learned_clss (remove_cls C S) = learned_clss S - {C}" and
    backtrack_lvl_remove_cls[simp]: "backtrack_lvl (remove_cls C S) = backtrack_lvl S" and
    conflicting_remove_cls[simp]: "conflicting (remove_cls C S) = conflicting S"
  unfolding remove_cls_def by auto

definition clauses :: "'st \<Rightarrow> 'v clauses" where
"clauses S = init_clss S \<union> learned_clss S"

lemma
  shows
    clauses_update_trail[simp]: "clauses (update_trail M S) = clauses S" and
    clauses_update_learned_clss[simp]: "clauses (update_learned_clss U S) = init_clss S \<union> U" and
    clauses_update_init_clss[simp]: "clauses (update_init_clss N S) = N \<union> learned_clss S" and
    clauses_update_backtrack_lvl[simp]: "clauses (update_backtrack_lvl k S) = clauses S" and
    clauses_update_conflicting[simp]: "clauses (update_conflicting D S) = clauses S" and
    clauses_remove_cls[simp]: "clauses (remove_cls C S) = clauses S - {C}" and
    clauses_add_cls[simp]: "clauses (add_cls C S) = clauses S \<union> {C}" and
    clauses_restart[simp]: "clauses (restart_state S) = clauses S" and
    clauses_init_state[simp]: "finite N \<Longrightarrow> clauses (init_state N) = N"
  unfolding clauses_def by auto

abbreviation update_state:: "'st \<Rightarrow> ('v, 'lvl, 'mark) marked_lit list \<times> 'v clauses \<times> 'v clauses
  \<times> nat \<times> 'v clause conflicting_clause \<Rightarrow> 'st" where
"update_state \<equiv> \<lambda>S (M, N, U, k, D).
  update_trail M (update_init_clss N (update_learned_clss U
    (update_backtrack_lvl k (update_conflicting D S))))"

abbreviation state ::  "'st \<Rightarrow> ('v, 'lvl, 'mark) marked_lit list \<times> 'v clauses \<times> 'v clauses
  \<times> nat \<times> 'v clause conflicting_clause" where
"state S \<equiv> (trail S, init_clss S, learned_clss S, backtrack_lvl S, conflicting S)"

abbreviation incr_lvl :: "'st \<Rightarrow> 'st" where
"incr_lvl S \<equiv> update_backtrack_lvl (backtrack_lvl S + 1) S"

lemma cls_of_mark_eq_cls_of_mark[iff]:
  "cls_of_mark C = cls_of_mark D \<longleftrightarrow> C = D"
  by (auto dest: arg_cong[of "cls_of_mark _" "cls_of_mark _" mark_of_cls])

lemma mark_of_cls_eq_mark_of_cls[iff]:
  "mark_of_cls C = mark_of_cls D \<longleftrightarrow> C = D"
  apply (rule iffI)
    apply (drule arg_cong[of "mark_of_cls _" "mark_of_cls _" cls_of_mark])
    apply simp
  apply simp
  done

end

section \<open>CDCL\<close>
subsection \<open>Auxiliary definitions\<close>
subsubsection \<open>Datatypes and access functions\<close>
type_synonym 'a cdcl_mark = "'a clause"
type_synonym cdcl_marked_level = nat

type_synonym 'v cdcl_marked_lit = "('v, cdcl_marked_level, 'v cdcl_mark) marked_lit"
type_synonym 'v cdcl_annoted_lits = "('v, cdcl_marked_level, 'v cdcl_mark) annoted_lits"
type_synonym 'v cdcl_state =
  "'v cdcl_annoted_lits \<times> 'v clauses \<times> 'v clauses \<times> nat \<times> 'v clause conflicting_clause"

abbreviation trail where
"trail \<equiv> (\<lambda>(M, N, U, k, D). M)"

abbreviation clauses where
"clauses \<equiv> \<lambda>(M, N, U, k, D). N"

abbreviation learned_clss where
"learned_clss \<equiv> \<lambda>(M, N, U, k, D). U"

abbreviation conflicting where
"conflicting \<equiv> \<lambda>(M, N, U, k, D). D"

abbreviation backtrack_lvl where
"backtrack_lvl \<equiv> \<lambda>(M, N, U, k, D). k"

abbreviation "S0_cdcl N \<equiv> (([], N, {}, 0, C_True):: 'v cdcl_state)"


interpretation default_cw: cw_state trail clauses learned_clss backtrack_lvl conflicting
  "\<lambda>M (_, N, U, k, D). (M, N, U, k, D)" "\<lambda>N (M, _, U, k, D). (M, N, U, k, D)"
  "\<lambda>U (M, N, _, k, D). (M, N, U, k, D)"
  "\<lambda>(k::nat) (M, N, U, _, D). (M, N, U, k, D)"
  "\<lambda>D (M, N, U, k, _). (M, N, U, k, D)"
  "\<lambda>N. ([], N, {}, 0, C_True)"
  id id "\<lambda>(_, N, U, _, _). ([], N, U, 0, C_True)"
  by unfold_locales auto

lemma trail_conv: "trail (M, N, U, k, D) = M" and
  clauses_conv: "clauses (M, N, U, k, D) = N" and
  learned_clss_conv: "learned_clss (M, N, U, k, D) = U" and
  conflicting_conv: "conflicting (M, N, U, k, D) = D" and
  backtrack_lvl_conv: "backtrack_lvl (M, N, U, k, D) = k"
  by auto

subsection \<open>CDCL Rules\<close>
text \<open>Because of the strategy we will later use, we distinguish propagate, conflict from the other
  rules\<close>
locale
  cdcl_cw_ops =
   cw_state trail init_clss learned_clss backtrack_lvl conflicting update_trail update_init_clss
   update_learned_clss update_backtrack_lvl update_conflicting init_state mark_of_cls cls_of_mark
   restart_state
  for
    trail :: "'st::equal \<Rightarrow> ('v, nat, 'mark) annoted_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow>'v clause conflicting_clause" and

    update_trail :: "('v, nat, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_init_clss :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_learned_clss :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause conflicting_clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    
    init_state :: "'v clauses \<Rightarrow> 'st" and
    mark_of_cls :: "'v clause \<Rightarrow> 'mark" and
    cls_of_mark :: "'mark \<Rightarrow> 'v clause" and
    restart_state :: "'st \<Rightarrow> 'st"
begin

inductive propagate :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
propagate_rule[intro]: "state S = (M, N, U, k, C_True) \<Longrightarrow>  C + {#L#} \<in> clauses S \<Longrightarrow> M \<Turnstile>as CNot C
  \<Longrightarrow> undefined_lit L (trail S)
  \<Longrightarrow> propagate S (cons_trail (Propagated L (C + {#L#})) S)"
inductive_cases propagateE[elim]: "propagate S T"
thm propagateE

inductive conflict ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" where
conflict_rule: "state S = (M, N, U, k, C_True) \<Longrightarrow> D \<in> clauses S \<Longrightarrow> M \<Turnstile>as CNot D
  \<Longrightarrow> conflict S (update_conflicting (C_Clause D) S)"

inductive_cases conflictE[elim]: "conflict S S'"

inductive backtrack ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" where
backtracking[intro]: "state S = (M, N, U, k, C_Clause (D + {#L#}))
  \<Longrightarrow> (Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M)
  \<Longrightarrow> get_level L M = k
  \<Longrightarrow> get_level L M = get_maximum_level (D+{#L#}) M
  \<Longrightarrow> get_maximum_level D M = i
  \<Longrightarrow> backtrack S (update_trail (Propagated L (mark_of_cls (D+{#L#})) # M1)
                    (add_cls (D + {#L#})
                       (update_backtrack_lvl i
                          (update_conflicting C_True S))))"
inductive_cases backtrackE[elim]: "backtrack S S'"
thm backtrackE

inductive decided ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" where
deciding[intro]: "state S = (M, N, U, k, C_True)
\<Longrightarrow> undefined_lit L M \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S)
\<Longrightarrow> decided S (cons_trail (Marked L (k+1)) (incr_lvl S))"
inductive_cases decidedE[elim]: "decided S S'"
thm decidedE

inductive skip :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
skipping[intro]: "state S = (Propagated L C' # M, N, U, k, C_Clause D) \<Longrightarrow>  -L \<notin># D \<Longrightarrow> D \<noteq> {#}
  \<Longrightarrow> skip S (tl_trail S)"
inductive_cases skipE[elim]: "skip S S'"
thm skipE

text \<open>@{term "get_maximum_level D (Propagated L (C + {#L#}) # M) = k \<or> k= 0"} is equivalent to
  @{term "get_maximum_level D (Propagated L (C + {#L#}) # M) = k"}\<close>
inductive resolve :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
resolving[intro]: "state S = (Propagated L (mark_of_cls (C + {#L#})) # M, N, U, k, C_Clause (D + {#-L#}))
  \<Longrightarrow> get_maximum_level D (Propagated L (mark_of_cls (C + {#L#})) # M) = k
  \<Longrightarrow> resolve S (update_conflicting (C_Clause (remdups_mset (D + C))) (tl_trail S))"
inductive_cases resolveE[elim]: "resolve S S'"
thm resolveE

inductive restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
restart: "state S = (M, N, U, k, C_True) \<Longrightarrow> \<not>M \<Turnstile>as clauses S
\<Longrightarrow> restart S (restart_state S)"
inductive_cases restartE[elim]: "restart S T"
thm restartE

text \<open>We add the condition @{term "C \<notin> init_clss S"}, to maintain consistency even without the
  strategy.\<close>
inductive forget :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
"state S = (M, N, U \<union> {C}, k, C_True) \<Longrightarrow> \<not>M \<Turnstile>as clauses S
  \<Longrightarrow> mark_of_cls C \<notin> set (get_all_mark_of_propagated (trail S))
  \<Longrightarrow> C \<notin> init_clss S
  \<Longrightarrow> C \<in> learned_clss S
  \<Longrightarrow> forget S (remove_cls C S)"
inductive_cases forgetE[elim]: "forget S T"

inductive cdcl_rf :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
restart: "restart S T \<Longrightarrow> cdcl_rf S T" |
forget: "forget S T \<Longrightarrow> cdcl_rf S T"

inductive cdcl_bj ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" where
skip[intro]: "skip S S' \<Longrightarrow> cdcl_bj S S'" |
resolve[intro]: "resolve S S' \<Longrightarrow> cdcl_bj S S'" |
backtrack[intro]: "backtrack S S' \<Longrightarrow> cdcl_bj S S'"

inductive_cases cdcl_bjE: "cdcl_bj S T"

inductive cdcl_o:: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
decided[intro]: "decided S S' \<Longrightarrow> cdcl_o S S'" |
bj[intro]: "cdcl_bj S S' \<Longrightarrow> cdcl_o S S'"

inductive cdcl :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
propagate: "propagate S S' \<Longrightarrow> cdcl S S'" |
conflict: "conflict S S' \<Longrightarrow> cdcl S S'" |
other: "cdcl_o S S' \<Longrightarrow> cdcl S S'"|
rf: "cdcl_rf S S' \<Longrightarrow> cdcl S S'"

lemma rtranclp_propagate_is_rtranclp_cdcl:
  "propagate\<^sup>*\<^sup>* S S' \<Longrightarrow> cdcl\<^sup>*\<^sup>* S S'"
  by (induction rule: rtranclp.induct) (fastforce dest!: propagate)+

lemma cdcl_all_rules_induct[consumes 1, case_names propagate conflict forget restart decided skip
    resolve backtrack]:
  fixes S  :: "'st"
  assumes cdcl: "cdcl S S'"
  and propagate: "\<And>S T. propagate S T \<Longrightarrow> P S T"
  and conflict:  "\<And>S T. conflict S T \<Longrightarrow> P S T"
  and forget:  "\<And>S T. forget S T \<Longrightarrow> P S T"
  and restart:  "\<And>S T. restart S T \<Longrightarrow> P S T"
  and decide:  "\<And>S T. decided S T \<Longrightarrow> P S T"
  and skip:  "\<And>S T. skip S T \<Longrightarrow> P S T"
  and resolve:  "\<And>S T. resolve S T \<Longrightarrow> P S T"
  and backtrack:  "\<And>S T. backtrack S T \<Longrightarrow> P S T"
  shows "P S S'"
  using assms(1)
proof (induct rule: cdcl.induct)
  case (propagate S S') note propagate = this(1)
  thus ?case using assms(2) by (auto)
next
  case (conflict S S')
  thus ?case using assms(3) by auto
next
  case (other S S')
  thus ?case
    proof (induct rule: cdcl_o.induct)
      case (decided T U)
      thus ?case using decide by auto
    next
      case (bj S S')
      thus ?case using assms(7-9) by (induction rule: cdcl_bj.induct) auto
    qed
next
  case (rf S S')
  thus ?case
    by (induct rule: cdcl_rf.induct) (fast dest: forget restart)+
qed

lemma cdcl_all_induct[consumes 1, case_names propagate conflict forget restart decided skip
    resolve backtrack]:
  fixes S  :: "'st"
  assumes
    cdcl: "cdcl S S'" and
    propagateH: "\<And>C L. C + {#L#} \<in> clauses S \<Longrightarrow> trail S \<Turnstile>as CNot C
      \<Longrightarrow> undefined_lit L (trail S) \<Longrightarrow> conflicting S = C_True
      \<Longrightarrow> P S (cons_trail (Propagated L (C + {#L#})) S)" and
    conflictH: "\<And>D. D \<in> clauses S \<Longrightarrow> conflicting S = C_True \<Longrightarrow> trail S \<Turnstile>as CNot D
      \<Longrightarrow> P S (update_conflicting (C_Clause D) S)" and
    forgetH: "\<And>C. \<not>trail S \<Turnstile>as clauses S
      \<Longrightarrow> mark_of_cls C \<notin> set (get_all_mark_of_propagated (trail S))
      \<Longrightarrow> C \<notin> init_clss S
      \<Longrightarrow> C \<in> learned_clss S
      \<Longrightarrow> conflicting S = C_True
      \<Longrightarrow> P S (remove_cls C S)" and
    restartH: "\<not>trail S \<Turnstile>as clauses S
      \<Longrightarrow> conflicting S = C_True
      \<Longrightarrow> P S (restart_state S)" and
    decideH: "\<And>L. conflicting S = C_True \<Longrightarrow>  undefined_lit L (trail S)
      \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S)
      \<Longrightarrow> P S (cons_trail (Marked L (backtrack_lvl S +1)) (incr_lvl S))" and
    skipH: "\<And>L C' M D. trail S = Propagated L C' # M
      \<Longrightarrow> conflicting S = C_Clause D \<Longrightarrow> -L \<notin># D \<Longrightarrow> D \<noteq> {#}
      \<Longrightarrow> P S (tl_trail S)" and
    resolveH: "\<And>L C M D.
      trail S = Propagated L (mark_of_cls (C + {#L#})) # M
      \<Longrightarrow> conflicting S = C_Clause (D + {#-L#})
      \<Longrightarrow> get_maximum_level D (Propagated L (mark_of_cls (C + {#L#})) # M) = backtrack_lvl S
      \<Longrightarrow> P S (update_conflicting (C_Clause (remdups_mset (D + C))) (tl_trail S))" and
    backtrackH: "\<And>K i M1 M2 L D.
      (Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))
      \<Longrightarrow> get_level L (trail S) = backtrack_lvl S
      \<Longrightarrow> conflicting S = C_Clause (D + {#L#})
      \<Longrightarrow> get_level L (trail S) = get_maximum_level (D+{#L#}) (trail S)
      \<Longrightarrow> get_maximum_level D (trail S) = i
      \<Longrightarrow> P S
            (update_trail (Propagated L (mark_of_cls (D+{#L#})) # M1)
                      (add_cls (D + {#L#})
                         (update_backtrack_lvl i
                            (update_conflicting C_True S))))"
  shows "P S S'"
  using cdcl
proof (induct S\<equiv>S S' rule: cdcl_all_rules_induct)
  case (propagate S')
  thus ?case by (elim propagateE) (frule propagateH; simp)
next
  case (conflict S')
  thus ?case by (elim conflictE) (frule conflictH; simp)
next
  case (restart S')
  thus ?case by (elim restartE) (frule restartH; simp)
next
  case (decided T)
  thus ?case by (elim decidedE) (frule decideH; simp)
next
  case (backtrack S')
  thus ?case  by (elim backtrackE) (frule backtrackH; simp)
next
  case (forget S')
  thus ?case using forgetH by auto
next
  case (skip S')
  thus ?case using skipH by auto
next
  case (resolve S')
  thus ?case by (elim resolveE) (frule resolveH; simp)
qed

lemma cdcl_o_induct[consumes 1, case_names decided skip resolve backtrack]:
  fixes S  :: "'st"
  assumes cdcl: "cdcl_o S T" and
    decideH: "\<And>L. conflicting S = C_True \<Longrightarrow>  undefined_lit L (trail S)
      \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S)
      \<Longrightarrow> P S (cons_trail (Marked L (backtrack_lvl S +1)) (incr_lvl S))" and
    skipH: "\<And>L C' M D. trail S = Propagated L C' # M
      \<Longrightarrow> conflicting S = C_Clause D \<Longrightarrow> -L \<notin># D \<Longrightarrow> D \<noteq> {#}
      \<Longrightarrow> P S (tl_trail S)" and
    resolveH: "\<And>L C M D.
      trail S = Propagated L (mark_of_cls (C + {#L#})) # M
      \<Longrightarrow> conflicting S = C_Clause (D + {#-L#})
      \<Longrightarrow> get_maximum_level D (Propagated L (mark_of_cls (C + {#L#})) # M) = backtrack_lvl S
      \<Longrightarrow> P S (update_conflicting (C_Clause (remdups_mset (D + C))) (tl_trail S))" and
    backtrackH: "\<And>K i M1 M2 L D.
      (Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))
      \<Longrightarrow> get_level L (trail S) = backtrack_lvl S
      \<Longrightarrow> conflicting S = C_Clause (D + {#L#})
      \<Longrightarrow> get_level L (trail S) = get_maximum_level (D+{#L#}) (trail S)
      \<Longrightarrow> get_maximum_level D (trail S) = i
      \<Longrightarrow> P S
            (update_trail (Propagated L (mark_of_cls (D+{#L#})) # M1)
                      (add_cls (D + {#L#})
                         (update_backtrack_lvl i
                            (update_conflicting C_True S))))"
  shows "P S T"
  using cdcl apply (induct S\<equiv>S T rule: cdcl_o.induct)
   using assms(2) apply auto[1]
  apply (elim cdcl_bjE skipE resolveE backtrackE)
    apply (frule skipH; simp)
   apply (frule resolveH; simp)
  apply (frule backtrackH; simp)
  done

lemma level_of_marked_ge_1:
  assumes "cdcl S S'"
  and "\<forall>L l. Marked L l \<in> set (trail S) \<longrightarrow> l > 0"
  shows "\<forall>L l. Marked L l \<in> set (trail S') \<longrightarrow> l > 0"
  using assms by (induct rule: cdcl_all_induct)
    (auto dest!: union_in_get_all_marked_decomposition_is_subset)

lemma cdcl_init_clss:
  "cdcl S T \<Longrightarrow> init_clss S = init_clss T"
  by (induct rule: cdcl_all_induct) auto

lemma rtranclp_cdcl_init_clss:
  "cdcl\<^sup>*\<^sup>* S T \<Longrightarrow> init_clss S = init_clss T"
  by (induct rule: rtranclp_induct) (auto dest: cdcl_init_clss)

subsection \<open>Invariants\<close>
subsubsection \<open>Properties of the trail\<close>
text \<open>We here establish that:
  * the marks are exactly 1..k where k is the level
  * the consistency of the trail
  * the fact that there is no duplicate in the trail.\<close>
lemma cdcl_o_bt:
  assumes "cdcl_o S S'"
  and "backtrack_lvl S = length (get_all_levels_of_marked (trail S))"
  and "get_all_levels_of_marked (trail S)
    = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])"
  shows "backtrack_lvl S' = length (get_all_levels_of_marked (trail S'))"
  using assms
proof (induct rule: cdcl_o_induct)
  case (backtrack K i M1 M2 L D) note decomp = this(1) and level = this(7)
  obtain c where M: "trail S = c @ M2 @ Marked K (i + 1) # M1" using decomp by auto
  have "rev (get_all_levels_of_marked (trail S))
    = [1..<1+ (length (get_all_levels_of_marked (trail S)))]"
    using level by (auto simp add: rev_swap[symmetric])
  thus ?case unfolding M by (auto dest!: append_cons_eq_upt_length simp del: upt_simps)
qed auto

lemma cdcl_rf_bt:
  assumes "cdcl_rf S S'"
  and "backtrack_lvl S = length (get_all_levels_of_marked (trail S))"
  and "get_all_levels_of_marked (trail S) = rev [1..<(1+length (get_all_levels_of_marked (trail S)))]"
  shows "backtrack_lvl S' = length (get_all_levels_of_marked (trail S'))"
  using assms by (induct rule: cdcl_rf.induct) (auto elim!: restartE)

lemma cdcl_bt:
  assumes "cdcl S S'"
  and "backtrack_lvl S = length (get_all_levels_of_marked (trail S))"
  and "get_all_levels_of_marked (trail S)
    = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])"
  shows "backtrack_lvl S' = length (get_all_levels_of_marked (trail S'))"
  using assms by (induct rule: cdcl.induct) (auto simp add: cdcl_o_bt cdcl_rf_bt)

lemma cdcl_bt_level':
  assumes "cdcl S S'"
  and "backtrack_lvl S = length (get_all_levels_of_marked (trail S))"
  and "get_all_levels_of_marked (trail S)
    = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])"
  shows "get_all_levels_of_marked (trail S')
    = rev ([1..<(1+length (get_all_levels_of_marked (trail S')))])"
  using assms
proof (induct rule: cdcl_all_induct)
  case (decided L)
  let ?k = "backtrack_lvl S"
  let ?M = "trail S"
  let ?M' = "Marked L (?k + 1) # trail S"
  have H: "get_all_levels_of_marked ?M = rev [Suc 0..<1+length (get_all_levels_of_marked ?M)]"
    using decided.prems by simp
  have k: "?k = length (get_all_levels_of_marked ?M)"
    using decided.prems by auto
  have "get_all_levels_of_marked ?M' = Suc ?k # get_all_levels_of_marked ?M" by simp
  hence "get_all_levels_of_marked ?M' = Suc ?k # rev [Suc 0..<1+length (get_all_levels_of_marked ?M)]"
    using H by auto
  moreover have "\<dots> = rev [Suc 0..< Suc (1+length (get_all_levels_of_marked ?M))]"
    unfolding k by simp
  finally show ?case by simp
next
  case (backtrack K i M1 M2 L D) note decomp = this(1) and confli = this(2) and
    all_marked = this(7) and bt_lvl = this(6)
  obtain c where M: "trail S = c @ M2 @ Marked K (i + 1) # M1" using decomp by auto
  have "get_all_levels_of_marked (rev (trail S))
    = [Suc 0..<2+length (get_all_levels_of_marked c) + (length (get_all_levels_of_marked M2)
                + length (get_all_levels_of_marked M1))]"
    using all_marked bt_lvl unfolding M by (auto simp add: rev_swap[symmetric] simp del: upt_simps)
  thus ?case by (auto simp add: rev_swap M dest!: append_cons_eq_upt(1) simp del: upt_simps)
qed auto

lemma backtrack_lit_skiped:
  assumes L: "get_level L (trail S) = backtrack_lvl S"
  and M1: "(Marked K (i + 1) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))"
  and no_dup: "no_dup (trail S)"
  and bt_l: "backtrack_lvl S = length (get_all_levels_of_marked (trail S))"
  and order: "get_all_levels_of_marked (trail S)
    = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])"
  shows "atm_of L \<notin> atm_of ` lits_of M1"
proof
  let ?M = "trail S"
  assume L_in_M1: "atm_of L \<in> atm_of ` lits_of M1"
  obtain c where Mc: "trail S = c @ M2 @ Marked K (i + 1) # M1" using M1 by blast
  have "atm_of L \<notin> atm_of ` lits_of c"
    using L_in_M1 no_dup mk_disjoint_insert unfolding Mc lits_of_def by force
  have g_M_eq_g_M1: "get_level L ?M = get_level L M1"
    using L_in_M1 unfolding Mc by auto
  have g: "get_all_levels_of_marked M1 = rev [1..<Suc i]"
    using order unfolding Mc
    by (auto simp del: upt_simps dest!: append_cons_eq_upt_length_i
             simp add: rev_swap[symmetric])
  hence "Max (set (0 # get_all_levels_of_marked (rev M1))) < Suc i" by auto
  hence "get_level L M1 < Suc i"
    using get_rev_level_less_max_get_all_levels_of_marked[of L 0 "rev M1"] by linarith
  moreover have "Suc i \<le> backtrack_lvl S" using bt_l by (simp add: Mc g)
  ultimately show False using L g_M_eq_g_M1 by auto
qed

lemma cdcl_distinctinv_1:
  assumes
    "cdcl S S'" and
    "no_dup (trail S)" and
    "backtrack_lvl S = length (get_all_levels_of_marked (trail S))" and
    "get_all_levels_of_marked (trail S) = rev [1..<1+length (get_all_levels_of_marked (trail S))]"
  shows "no_dup (trail S')"
  using assms
proof (induct rule: cdcl_all_induct)
  case (backtrack K i M1 M2 L D) note decomp = this(1) and L = this(2) and n_d = this(6)
  obtain c where Mc: "trail S = c @ M2 @ Marked K (i + 1) # M1"
    using decomp by auto
  have "no_dup (M2 @ Marked K (i + 1) # M1)"
    using Mc n_d by fastforce
  moreover have "atm_of L \<notin> (\<lambda>l. atm_of (lit_of l)) ` set M1"
    using backtrack_lit_skiped[of L S K i M1 M2] L decomp backtrack.prems
    by (fastforce simp add: lits_of_def)
  ultimately show ?case by simp
qed (auto simp add: defined_lit_map)


lemma cdcl_consistent_inv_2:
  assumes
    "cdcl S S'" and
    "no_dup (trail S)" and
    "backtrack_lvl S = length (get_all_levels_of_marked (trail S))" and
    "get_all_levels_of_marked (trail S) = rev [1..<1+length (get_all_levels_of_marked (trail S))]"
  shows "consistent_interp (lits_of (trail S'))"
  using cdcl_distinctinv_1[OF assms] distinctconsistent_interp by fast

lemma cdcl_finite_init_cls:
  fixes S S' :: 'st
  assumes
    "cdcl S S'" and
    "finite (init_clss S)"
  shows "finite (init_clss S')"
  using assms by (induction rule: cdcl_all_induct) auto

lemma rtranclp_cdcl_finite_init_clss:
  fixes S S' :: 'st
  assumes
    "cdcl\<^sup>*\<^sup>* S S'" and
    "finite (init_clss S)"
  shows "finite (init_clss S')"
  using assms by (induction rule: rtranclp_induct) (auto intro: cdcl_finite_init_cls)

text \<open>We write @{term "1+length (get_all_levels_of_marked (trail S))"} instead of
  @{term "backtrack_lvl S"} to avoid non termination of rewriting.\<close>
definition "cdcl_M_level_inv (S:: 'st) \<longleftrightarrow>
  consistent_interp (lits_of (trail S))
  \<and> no_dup (trail S)
  \<and> backtrack_lvl S = length (get_all_levels_of_marked (trail S))
  \<and> get_all_levels_of_marked (trail S)
      = rev ([1..<1+length (get_all_levels_of_marked (trail S))])"

lemma cdcl_M_level_inv_decomp[dest]:
  assumes "cdcl_M_level_inv S"
  shows "consistent_interp (lits_of (trail S))"
  and "no_dup (trail S)"
  and "length (get_all_levels_of_marked (trail S)) = backtrack_lvl S"
  and "get_all_levels_of_marked (trail S) = rev ([Suc 0..< Suc 0+backtrack_lvl S])"
  using assms unfolding cdcl_M_level_inv_def by fastforce+

lemma cdcl_consistent_inv:
  fixes S S' :: 'st
  assumes
    "cdcl S S'" and
    "cdcl_M_level_inv S"
  shows "cdcl_M_level_inv S'"
  using assms cdcl_consistent_inv_2 cdcl_distinctinv_1 cdcl_bt cdcl_bt_level'
  unfolding cdcl_M_level_inv_def by blast+

lemma rtranclp_cdcl_consistent_inv:
  assumes "cdcl\<^sup>*\<^sup>* S S'"
  and "cdcl_M_level_inv S"
  shows "cdcl_M_level_inv S'"
  using assms by (induct rule: rtranclp_induct)
  (auto intro: cdcl_consistent_inv)

lemma cdcl_M_level_inv_S0_cdcl[simp]:
    "finite N \<Longrightarrow> cdcl_M_level_inv (init_state N)"
  unfolding cdcl_M_level_inv_def by auto

subsubsection \<open>Learned Clause\<close>
text \<open>This invariant shows that:
  \<^item> the learned clauses are entailed by the initial set of clauses.
  \<^item> the conflicting clause is entailed by the initial set of clauses.
  \<^item> the marks are entailed by the clauses. A more precise version would be to show that either
  these marked are learned or are in the set of clauses\<close>

definition "cdcl_learned_clause (S:: 'st) \<longleftrightarrow>
  (init_clss S \<Turnstile>ps learned_clss S
  \<and> (\<forall>T. conflicting S = C_Clause T \<longrightarrow> init_clss S \<Turnstile>p T)
  \<and> set (get_all_mark_of_propagated (trail S)) \<subseteq> mark_of_cls ` clauses S)"

(*propo 2.9.6.2*)
lemma cdcl_learned_clause_S0_cdcl[simp]:
   "finite N \<Longrightarrow> cdcl_learned_clause (init_state N)"
  unfolding cdcl_learned_clause_def by auto

(* TODO Move *)
lemma union_trus_clss_clss[simp]: "A \<union> B \<Turnstile>ps B"
  unfolding true_clss_clss_def by auto

lemma true_clss_clss_remove[simp]:
  "A \<Turnstile>ps B \<Longrightarrow> A\<Turnstile>ps B - C"
  by (metis Un_Diff_Int true_clss_clss_union_and)

lemma cdcl_learned_clss:
  assumes "cdcl S S'"
  and "cdcl_learned_clause S"
  shows "cdcl_learned_clause S'"
  using assms(1,2)
proof (induct rule: cdcl_all_induct)
  case (backtrack K i M1 M2 L D) note decomp = this(1) and confl = this(3) and learned = this(6)
  show ?case
    using decomp confl learned unfolding cdcl_learned_clause_def
    by (auto dest!: get_all_marked_decomposition_exists_prepend
      simp: clauses_def dest: true_clss_clss_left_right)
next
  case (resolve L C M D) note trail = this(1) and confl = this(2) and lvl = this(3) and
    learned = this(4)
  moreover
    have "init_clss S \<Turnstile>ps learned_clss S"
      using learned trail unfolding cdcl_learned_clause_def clauses_def by auto
    hence "init_clss S \<Turnstile>p C + {#L#}"
      using trail learned  unfolding cdcl_learned_clause_def clauses_def
      by (auto dest: true_clss_clss_in_imp_true_clss_cls)
  ultimately show ?case
    by (auto dest: mk_disjoint_insert true_clss_clss_left_right
      simp add: cdcl_learned_clause_def clauses_def
      intro: true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or)
qed (auto dest: mk_disjoint_insert
      simp add: cdcl_learned_clause_def clauses_def true_clss_clss_left_right)

lemma rtranclp_cdcl_learned_clss:
  assumes "cdcl\<^sup>*\<^sup>* S S'"
  and "cdcl_learned_clause S"
  shows "cdcl_learned_clause S'"
  using assms by (induction) (auto dest: cdcl_learned_clss)

subsubsection \<open>No alien atom in the state\<close>
text \<open>This invariant means that all the literals are in the set of clauses.\<close>
definition "no_strange_atm S' \<longleftrightarrow> (
    (\<forall>T. conflicting S' = C_Clause T \<longrightarrow> atms_of T \<subseteq> atms_of_m (init_clss S'))
  \<and> (\<forall>L mark. Propagated L mark \<in> set (trail S')
      \<longrightarrow> atms_of (cls_of_mark mark) \<subseteq> atms_of_m (init_clss S'))
  \<and> atms_of_m (learned_clss S') \<subseteq> atms_of_m (init_clss S')
  \<and> atm_of ` (lits_of (trail S')) \<subseteq> atms_of_m (init_clss S'))"

lemma no_strange_atm_decomp:
  assumes "no_strange_atm S"
  shows "conflicting S = C_Clause T \<Longrightarrow> atms_of T \<subseteq> atms_of_m (init_clss S)"
  and "(\<forall>L mark. Propagated L mark \<in> set (trail S)
    \<longrightarrow> atms_of (cls_of_mark mark) \<subseteq> atms_of_m (init_clss S))"
  and "atms_of_m (learned_clss S) \<subseteq> atms_of_m (init_clss S)"
  and "atm_of ` (lits_of (trail S)) \<subseteq> atms_of_m (init_clss S)"
  using assms unfolding no_strange_atm_def by blast+

lemma no_strange_atm_S0 [simp]: "finite N \<Longrightarrow> no_strange_atm (init_state N)"
  unfolding no_strange_atm_def by auto

lemma cdcl_no_strange_atm_explicit:
  assumes
    "cdcl S S'" and
    "\<forall>T. conflicting S = C_Clause T \<longrightarrow> atms_of T \<subseteq> atms_of_m (init_clss S)" and
    "\<forall>L mark. Propagated L mark \<in> set (trail S)
      \<longrightarrow> atms_of (cls_of_mark mark) \<subseteq> atms_of_m (init_clss S)" and
    "atms_of_m (learned_clss S) \<subseteq> atms_of_m (init_clss S)" and
    "atm_of ` (lits_of (trail S)) \<subseteq> atms_of_m (init_clss S)"
  shows "(\<forall>T. conflicting S' = C_Clause T \<longrightarrow> atms_of T \<subseteq> atms_of_m (init_clss S')) \<and>
   (\<forall>L mark. Propagated L mark \<in> set (trail S')
     \<longrightarrow> atms_of (cls_of_mark mark) \<subseteq> atms_of_m (init_clss S')) \<and>
   atms_of_m (learned_clss S') \<subseteq> atms_of_m (init_clss S') \<and>
   atm_of ` (lits_of (trail S')) \<subseteq> atms_of_m (init_clss S')" (is "?C S' \<and> ?M S' \<and> ?U S' \<and> ?V S'")
  using assms(1-5)
proof (induct rule: cdcl_all_induct)
  case (propagate C L) note confl = this(4)
  have "?C (cons_trail (Propagated L (C + {#L#})) S)" using confl by auto
  moreover have "?M (cons_trail (Propagated L (C + {#L#})) S)"
    using propagate.prems(2,3) \<open>C + {#L#} \<in> clauses S \<close>
    by (fastforce simp add: atms_of_m_def clauses_def)
  moreover have "?U  (cons_trail (Propagated L (C + {#L#})) S)"
    using propagate.prems(3) by auto
  moreover have "?V (cons_trail (Propagated L (C + {#L#})) S)"
    using \<open>C + {#L#} \<in> clauses S\<close> propagate.prems(3,4) unfolding lits_of_def clauses_def by auto
  ultimately show ?case by blast
next
  case (decided L)
  thus ?case unfolding clauses_def by auto
next
  case (skip L C M D)
  thus ?case by auto
next
  case (conflict D)
  have "atm_of ` set_mset D \<subseteq> \<Union>(atms_of ` (clauses S))"
    using \<open>D \<in> clauses S\<close> conflict.prems(3) by (auto simp add: atms_of_def atms_of_m_def)
  moreover
    {
       fix xa :: "'v literal"
       assume a1: "(\<Union>x\<in>learned_clss S. atms_of x) \<subseteq> (\<Union>x\<in>init_clss S. atms_of x)"
       assume a2: "xa \<in># D"
       have "UNION (local.clauses S) atms_of = UNION (init_clss S) atms_of"
         using a1 by (metis (no_types) UN_Un clauses_def sup.orderE) (* 109 ms *)
       hence "\<exists>m\<in>init_clss S. atm_of xa \<in> atms_of m"
         using a2 by (metis UN_iff atm_of_lit_in_atms_of conflict.hyps(1)) (* 181 ms *)
    } note H = this
  ultimately show ?case using conflict.prems unfolding atms_of_def atms_of_m_def clauses_def
    by (auto simp add: H)
next
  case restart
  thus ?case by auto
next
  case (forget C) note C[simp] = this(3) and C_le[simp] = this(4) and confl = this(5) and
    atm_mark = this(7) and atm_le = this(8) and atm_trail = this(9)
  show ?case unfolding clauses_def apply standard
    using confl unfolding clauses_def apply auto[]
    apply standard
     using atm_mark apply auto[]
    apply standard
     using atm_le atms_of_m_remove_subset[of "learned_clss S" "{C}"] apply auto[]
    using atm_trail apply (auto simp: clauses_def lits_of_def)[]
  done
next
  case (backtrack K i M1 M2 L D) note decomp = this(1) and confl = this(3)
  let ?T = "update_trail (Propagated L (mark_of_cls (D+{#L#})) # M1)
                      (add_cls (D + {#L#})
                         (update_backtrack_lvl i
                            (update_conflicting C_True S)))"
  have "?C ?T"
    using backtrack.prems(3) by simp
  moreover have "set M1 \<subseteq> set (trail S)"
    using backtrack.hyps(1) by auto
  hence M: "?M ?T"
    using backtrack.prems(1,2) confl by (auto simp add: image_subset_iff clauses_def)
  moreover have "?U ?T"
    using backtrack.prems(1,3) confl unfolding clauses_def by auto
  moreover have "?V ?T"
    using M backtrack.prems(4) backtrack.hyps(1) by fastforce
  ultimately show ?case by blast
next
  case (resolve L C M D) note trail = this(1) and confl = this(2)
  let ?T = "update_conflicting (C_Clause (remdups_mset (D + C))) (tl_trail S)"
  have "?C ?T"
    using confl trail resolve.prems(1,2) by simp
  moreover have  "?M ?T"
    using confl trail resolve.prems(1,2) by auto
  moreover have "?U ?T"
    using resolve.prems(1,3) by auto
  moreover have "?V ?T"
    using confl trail resolve.prems(4) by auto
  ultimately show ?case by blast
qed

lemma cdcl_no_strange_atm_inv:
  assumes "cdcl S S'" and "no_strange_atm S"
  shows "no_strange_atm S'"
  using cdcl_no_strange_atm_explicit[OF assms(1)] assms(2) unfolding no_strange_atm_def by fast

lemma rtranclp_cdcl_no_strange_atm_inv:
  assumes "cdcl\<^sup>*\<^sup>* S S'" and "no_strange_atm S"
  shows "no_strange_atm S'"
  using assms by induction (auto intro: cdcl_no_strange_atm_inv rtranclp_cdcl_finite_init_clss)

subsubsection \<open>No duplicates all around\<close>
text \<open>This invariant shows that there is no duplicate (no literal appearing twice in the formula).
  The last part could be proven using the previous invariant moreover.\<close>
definition "distinct_cdcl_state (S::'st)
  \<longleftrightarrow> ((\<forall>T. conflicting S = C_Clause T \<longrightarrow> distinct_mset T)
    \<and> distinct_mset_set (learned_clss S)
    \<and> distinct_mset_set (init_clss S)
    \<and> (\<forall>L mark. (Propagated L mark \<in> set (trail S) \<longrightarrow> distinct_mset (cls_of_mark mark))))"

lemma distinct_cdcl_state_decomp:
  assumes "distinct_cdcl_state (S::'st)"
  shows "\<forall>T. conflicting S = C_Clause T \<longrightarrow> distinct_mset T"
  and "distinct_mset_set (learned_clss S)"
  and "distinct_mset_set (init_clss S)"
  and "\<forall>L mark. (Propagated L mark \<in> set (trail S) \<longrightarrow> distinct_mset (cls_of_mark mark))"
  using assms unfolding distinct_cdcl_state_def by blast+

lemma distinct_cdcl_state_decomp_2:
  assumes "distinct_cdcl_state (S::'st)"
  shows "conflicting S = C_Clause T \<Longrightarrow> distinct_mset T"
  using assms unfolding distinct_cdcl_state_def by auto

lemma distinct_cdcl_state_S0_cdcl[simp]:
  "distinct_mset_set N \<Longrightarrow> finite N \<Longrightarrow> distinct_cdcl_state (init_state N)"
  unfolding distinct_cdcl_state_def by auto

lemma distinct_cdcl_state_inv:
  assumes
    "cdcl S S'" and
    "distinct_cdcl_state S"
  shows "distinct_cdcl_state S'"
  using assms
proof (induct rule: cdcl_all_induct)
  case (backtrack K i M1 M2 L D)
  thus ?case
    unfolding distinct_cdcl_state_def by (fastforce dest: get_all_marked_decomposition_incl)
qed (auto simp add: distinct_cdcl_state_def distinct_mset_set_def clauses_def)

lemma rtanclp_distinct_cdcl_state_inv:
  assumes
    "cdcl\<^sup>*\<^sup>* S S'" and
    "distinct_cdcl_state S"
  shows "distinct_cdcl_state S'"
  using assms apply (induct rule: rtranclp.induct)
  using distinct_cdcl_state_inv by blast+

subsubsection \<open>Conflicts and co\<close>
text \<open>This invariant shows that each mark contains a contradiction only related to the previously
  defined variable.\<close>
abbreviation every_mark_is_a_conflict :: "'st \<Rightarrow> bool" where
"every_mark_is_a_conflict S \<equiv>
 \<forall>L mark a b. a @ Propagated L mark # b = (trail S)
   \<longrightarrow> (b \<Turnstile>as CNot (cls_of_mark mark - {#L#}) \<and> L \<in># cls_of_mark mark)"

definition "cdcl_conflicting S \<equiv>
  (\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T)
  \<and> every_mark_is_a_conflict S"

lemma backtrack_atms_of_D_in_M1:
  assumes bt: "backtrack S (update_trail (Propagated L (mark_of_cls (D+{#L#})) # M1)
                      (add_cls (D + {#L#})
                         (update_backtrack_lvl i
                            (update_conflicting C_True S))))"
  and confl: "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T"
  and lev: "cdcl_M_level_inv S"
  shows "atms_of D \<subseteq> atm_of ` lits_of M1"
proof (rule ccontr)
  obtain K M2 i where
    i: "i = get_maximum_level D (trail S)" and
    decomp: "(Marked K (Suc i) # M1, M2)
       \<in> set (get_all_marked_decomposition (trail S))" and
    "get_level L (trail S) = get_maximum_level (D + {#L#}) (trail S)" and
    S_lvl: "backtrack_lvl S = get_maximum_level (D + {#L#}) (trail S)" and
    S_confl: "conflicting S = C_Clause (D + {#L#})"
    using bt by (fastforce simp: st_equal elim!: backtrackE)

  let ?k = "get_maximum_level (D + {#L#}) (trail S)"
  have "trail S \<Turnstile>as CNot D" using confl S_confl by auto
  hence vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of (trail S)" unfolding atms_of_def
    by (meson image_subsetI mem_set_mset_iff true_annots_CNot_all_atms_defined)

  obtain M0 where M: "trail S = M0 @ M2 @ Marked K (Suc i) # M1"
    using decomp by auto

  have max: "get_maximum_level (D + {#L#}) (trail S)
    = length (get_all_levels_of_marked (M0 @ M2 @ Marked K (Suc i) # M1))"
    using lev unfolding cdcl_M_level_inv_def S_lvl M by simp
  assume a: "\<not> ?thesis"
  then obtain L' where
    L': "L' \<in> atms_of D" and
    L'_notin_M1: "L' \<notin> atm_of ` lits_of M1" by auto
  then have L'_in: "L' \<in> atm_of ` lits_of (M0 @ M2 @ Marked K (i + 1) # [])"
    using vars_of_D unfolding M by force
  then obtain L'' where
    "L'' \<in># D" and
    L'': "L' = atm_of L''"
    using L' L'_notin_M1 unfolding atms_of_def by auto
  have "get_level L'' (trail S) = get_rev_level L'' (Suc i) (Marked K (Suc i) # rev M2 @ rev M0)"
    using L'_notin_M1 L'' M by (auto simp del: get_rev_level.simps)
  have "get_all_levels_of_marked (trail S) = rev [1..<1+?k]"
    using lev S_lvl unfolding cdcl_M_level_inv_def by auto
  hence "get_all_levels_of_marked (M0 @ M2)
    = rev [Suc (Suc i)..<Suc (get_maximum_level (D + {#L#}) (trail S))]"
    unfolding M by (auto simp:rev_swap[symmetric] dest!: append_cons_eq_upt_length_i_end)

  hence M: "get_all_levels_of_marked M0 @ get_all_levels_of_marked M2
    = rev [Suc (Suc i)..<Suc (length (get_all_levels_of_marked (M0 @ M2 @ Marked K (Suc i) # M1)))]"
    unfolding max unfolding M by simp

  have "get_rev_level L'' (Suc i) (Marked K (Suc i) # rev (M0 @ M2))
    \<ge> Min (set ((Suc i) # get_all_levels_of_marked (Marked K (Suc i) # rev (M0 @ M2))))"
    using get_rev_level_ge_min_get_all_levels_of_marked[of L''
      "rev (M0 @ M2 @ [Marked K (Suc i)])" "Suc i"] L'_in
    unfolding L'' by (fastforce simp add: lits_of_def)
  also have "Min (set ((Suc i) # get_all_levels_of_marked (Marked K (Suc i) # rev (M0 @ M2))))
    = Min (set ((Suc i) # get_all_levels_of_marked (rev (M0 @ M2))))" by auto
  also have "\<dots> = Min (set ((Suc i) # get_all_levels_of_marked M0 @ get_all_levels_of_marked M2))"
    by (simp add: Un_commute)
  also have "\<dots> =  Min (set ((Suc i) # [Suc (Suc i)..<2 + length (get_all_levels_of_marked M0)
    + (length (get_all_levels_of_marked M2) + length (get_all_levels_of_marked M1))]))"
    unfolding M by (auto simp add: Un_commute)
  also have "\<dots> = Suc i" by (auto intro: Min_eqI)
  finally have "get_rev_level L'' (Suc i) (Marked K (Suc i) # rev (M0 @ M2)) \<ge> Suc i" .
  hence "get_level L'' (trail S) \<ge> i + 1"
    using \<open>get_level L'' (trail S) = get_rev_level L'' (Suc i) (Marked K (Suc i) # rev M2 @ rev M0)\<close>
    by simp
  hence "get_maximum_level D (trail S) \<ge> i + 1"
    using get_maximum_level_ge_get_level[OF \<open>L'' \<in># D\<close>, of "trail S"] by auto
  thus False using i by auto
qed

lemma distinct_atms_of_incl_not_in_other:
    assumes a1: "no_dup (M @ M')"
    and a2: "atms_of D \<subseteq> atm_of ` lits_of M'"
    shows"\<forall>x\<in>atms_of D. x \<notin> atm_of ` lits_of M"
proof -
  { fix aa :: 'a
    have ff1: "\<And>l ms. |l| \<notin>\<^sub>l |ms| \<or> atm_of l \<in> set (map (\<lambda>m. atm_of (lit_of (m::('a, 'b, 'c) marked_lit))) ms)"
      by (simp add: defined_lit_map)
    have ff2: "\<And>a. a \<notin> atms_of D \<or> a \<in> atm_of ` lits_of M'"
      using a2 by (meson subsetCE)
    have ff3: "\<And>a. a \<notin> set (map (\<lambda>m. atm_of (lit_of m)) M') \<or> a \<notin> set (map (\<lambda>m. atm_of (lit_of m)) M)"
      using a1 by (metis (lifting) IntI distinct_append empty_iff map_append)
    have "\<forall>L a f. \<exists>l. ((a::'a) \<notin> f ` L \<or> (l::'a literal) \<in> L) \<and> (a \<notin> f ` L \<or> f l = a)"
      by blast
    hence "aa \<notin> atms_of D \<or> aa \<notin> atm_of ` lits_of M"
      using ff3 ff2 ff1 by (metis (no_types) Marked_Propagated_in_iff_in_lits_of) }
  thus ?thesis
    by blast
qed

lemma cdcl_propagate_is_conclusion:
  assumes
    "cdcl S S'" and
    "all_decomposition_implies (init_clss S) (get_all_marked_decomposition (trail S))" and
    "cdcl_learned_clause S" and
    "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    "cdcl_M_level_inv S" and
    "no_strange_atm S"
  shows "all_decomposition_implies (init_clss S') (get_all_marked_decomposition (trail S'))"
  using assms
proof (induct rule: cdcl_all_induct)
  case restart
  thus ?case by auto
next
  case forget
  thus ?case by auto
next
  case conflict
  thus ?case by auto
next
  case (resolve L C M D) note tr = this(1)
  let ?decomp = "get_all_marked_decomposition M"
  have M: "set ?decomp = insert (hd ?decomp) (set (tl ?decomp))"
    by (cases ?decomp) auto
  show ?case
    using resolve.prems(1) tr unfolding all_decomposition_implies_def
    by (cases "hd (get_all_marked_decomposition M)")
       (auto simp: M)
next
  case (skip L C' M D) note tr = this(1)
  have M: "set (get_all_marked_decomposition M) = insert (hd (get_all_marked_decomposition M)) (set (tl (get_all_marked_decomposition M)))"
    by (cases "get_all_marked_decomposition M") auto
  show ?case
    using skip.prems(1) tr unfolding all_decomposition_implies_def
    by (cases "hd (get_all_marked_decomposition M)")
       (auto simp add: M)
next
  case decided note S = this(1)
  show ?case using decided.prems(1) unfolding S all_decomposition_implies_def by auto
next
  case (propagate C L) note propa = this(2) and decomp = this(5) and alien = this(9)
  obtain a y where ay: "hd (get_all_marked_decomposition (trail S)) = (a, y)"
    by (cases "hd (get_all_marked_decomposition (trail S))")
  hence M: "trail S = y @ a" using get_all_marked_decomposition_decomp by blast
  have M': "set (get_all_marked_decomposition (trail S))
    = insert (a, y) (set (tl (get_all_marked_decomposition (trail S))))"
    using ay by (cases "get_all_marked_decomposition (trail S)") auto
  have "(\<lambda>a. {#lit_of a#}) ` set a \<union> (init_clss S) \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set y"
    using decomp ay unfolding all_decomposition_implies_def
    by (cases "get_all_marked_decomposition (trail S)") fastforce+
  hence a_Un_N_M: "(\<lambda>a. {#lit_of a#}) ` set a \<union> (init_clss S) \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set (trail S)"
    unfolding M by (auto simp add: all_in_true_clss_clss image_Un)

  have "(\<lambda>a. {#lit_of a#}) ` set a \<union> (init_clss S) \<Turnstile>p {#L#}" (is "?I \<Turnstile>p _")
    proof (rule true_clss_cls_plus_CNot)
      show "?I \<Turnstile>p C + {#L#}"
        using propa propagate.prems unfolding M
        by (metis UnE cdcl_learned_clause_def clauses_def propagate.hyps(1) true_clss_cls_in
          true_clss_clss_in_imp_true_clss_cls true_clss_cs_mono_l2)
    next
      have "(\<lambda>m. {#lit_of m#}) ` set (trail S) \<Turnstile>ps CNot C"
        using \<open>(trail S) \<Turnstile>as CNot C\<close> true_annots_true_clss_clss by blast
      thus "?I \<Turnstile>ps CNot C"
        using a_Un_N_M true_clss_clss_left_right true_clss_clss_union_l_r by blast
    qed
  moreover have "\<And>aa b.
      \<forall> (Ls, seen)\<in>set (get_all_marked_decomposition (y @ a)).
        (\<lambda>a. {#lit_of a#}) ` set Ls \<union> init_clss S \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen
    \<Longrightarrow> (aa, b) \<in> set (tl (get_all_marked_decomposition (y @ a)))
    \<Longrightarrow> (\<lambda>a. {#lit_of a#}) ` set aa \<union> init_clss S \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set b"
    by (metis (no_types, lifting) case_prod_conv get_all_marked_decomposition_never_empty_sym
      list.collapse list.set_intros(2))

  ultimately show ?case
    using decomp unfolding ay all_decomposition_implies_def
    using M \<open>(\<lambda>a. {#lit_of a#}) ` set a \<union> init_clss S \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set y\<close> ay by auto
next
  case (backtrack K i M1 M2 L D) note decomp = this(1) and lev_L = this(2) and confl = this(3)
  have "\<forall>l \<in> set M2. \<not>is_marked l"
    using get_all_marked_decomposition_snd_not_marked backtrack.hyps(1) by blast
  obtain M0 where M: "trail S = M0 @ M2 @ Marked K (i + 1) # M1"
    using backtrack.hyps(1) by auto
  show ?case unfolding all_decomposition_implies_def
    proof
      fix x
      assume "x \<in>set (get_all_marked_decomposition
        (trail (update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1)
          (add_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True S))))))"
      hence x: "x \<in> set (get_all_marked_decomposition (Propagated L (mark_of_cls(D + {#L#})) # M1))"
        by simp
      let ?m = "get_all_marked_decomposition (Propagated L (mark_of_cls(D + {#L#})) # M1)"
      let ?hd = "hd ?m"
      let ?tl = "tl ?m"
      have "x = ?hd \<or> x \<in> set ?tl"
        using x by (case_tac "?m") auto
      moreover {
        assume "x \<in> set ?tl"
        hence "x \<in> set (get_all_marked_decomposition (trail S))"
          using tl_get_all_marked_decomposition_skip_some[of x] by (simp add: list.set_sel(2) M)
        hence "case x of (Ls, seen) \<Rightarrow> (\<lambda>a. {#lit_of a#}) ` set Ls
                \<union> init_clss (update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1)
                   (add_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True S))))
                \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen"
          using \<open>x \<in> set ?m\<close> backtrack.prems(1) unfolding all_decomposition_implies_def M
          using \<open>x \<in> set (get_all_marked_decomposition (trail S))\<close> all_decomposition_implies_def
          backtrack.prems(2) by fastforce
      }
      moreover {
        assume "x = ?hd"
        obtain M1' M1'' where M1: "hd (get_all_marked_decomposition M1) = (M1', M1'')"
          by (cases "hd (get_all_marked_decomposition M1)")
        hence x': "x = (M1', Propagated L (mark_of_cls (D + {#L#})) # M1'')"
          using \<open>x= ?hd\<close> by auto
        have "(M1', M1'') \<in> set (get_all_marked_decomposition (trail S))"
          using M1[symmetric] hd_get_all_marked_decomposition_skip_some[OF M1[symmetric],
            of "M0 @ M2" _ "i+1"] unfolding M by fastforce
        hence 1: "(\<lambda>a. {#lit_of a#}) ` set M1' \<union> init_clss S \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set M1''"
          using backtrack.prems(1) unfolding all_decomposition_implies_def by auto
        moreover
          have "trail S \<Turnstile>as CNot D" using backtrack.prems(3) confl by auto
          hence vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of (trail S)"
            unfolding atms_of_def
            by (meson image_subsetI mem_set_mset_iff true_annots_CNot_all_atms_defined)
          have "backtrack S  (update_trail (Propagated L (mark_of_cls (D+{#L#})) # M1)
                      (add_cls (D + {#L#})
                         (update_backtrack_lvl i
                            (update_conflicting C_True S))))"
            using backtrack.hyps(4) backtrack.hyps(5) backtrack.intros confl decomp lev_L by auto
          hence vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of M1"
            using backtrack_atms_of_D_in_M1 backtrack.prems
               by auto
          have "no_dup (trail S)" using backtrack.prems(4) by auto
          hence vars_in_M1:
            "\<forall>x \<in> atms_of D. x \<notin> atm_of ` lits_of (M0 @ M2 @ Marked K (i + 1) # [])"
            using vars_of_D distinct_atms_of_incl_not_in_other[of "M0 @M2 @ Marked K (i + 1) # []"
              M1]
            unfolding M by auto
          have "M1 \<Turnstile>as CNot D"
            using vars_in_M1 true_annots_remove_if_notin_vars[of "M0 @ M2 @ Marked K (i + 1) # []"
              M1 "CNot D"] \<open>trail S \<Turnstile>as CNot D\<close> unfolding M lits_of_def by simp
          have "M1 = M1'' @ M1'" by (simp add: M1 get_all_marked_decomposition_decomp)
          have TT: "(\<lambda>a. {#lit_of a#}) ` set M1' \<union> (init_clss S) \<Turnstile>ps CNot D"
            using true_annots_true_clss_cls[OF \<open>M1 \<Turnstile>as CNot D\<close>] true_clss_clss_left_right[OF 1,
              of "CNot D"] unfolding \<open>M1 = M1'' @ M1'\<close> by (auto simp add: inf_sup_aci(5,7))
          have "init_clss S \<Turnstile>p D + {#L#}"
            using backtrack.prems(2) cdcl_learned_clause_def confl by blast
          hence T: "(\<lambda>a. {#lit_of a#}) ` set M1' \<union> (init_clss S) \<Turnstile>p D + {#L#}" by auto
          have "atms_of (D + {#L#}) \<subseteq> atms_of_m (clauses S)"
            using backtrack.prems(5) confl unfolding no_strange_atm_def clauses_def by auto
          hence "(\<lambda>a. {#lit_of a#}) ` set M1' \<union> (init_clss S) \<Turnstile>p {#L#}"
            using true_clss_cls_plus_CNot[OF T TT] by auto
        ultimately
          have "case x of (Ls, seen) \<Rightarrow>(\<lambda>a. {#lit_of a#}) ` set Ls
            \<union> init_clss (update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1)
              (add_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True S))))
            \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen" unfolding x' by simp
      }
      ultimately show "case x of (Ls, seen) \<Rightarrow> (\<lambda>a. {#lit_of a#}) ` set Ls
           \<union> init_clss (update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1)
             (add_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True S))))
         \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen" by blast
    qed
qed

lemma cdcl_propagate_is_false:
  assumes "cdcl S S'" and
    "all_decomposition_implies (init_clss S) (get_all_marked_decomposition (trail S))" and
    "cdcl_learned_clause S" and
    "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    "cdcl_M_level_inv S" and
    "no_strange_atm S" and
    "every_mark_is_a_conflict S"
  shows "every_mark_is_a_conflict S'"
  using assms
proof (induct rule: cdcl_all_induct)
  case (propagate C L)
  show ?case
    proof (intro allI impI)
      fix L' mark a b
      assume "a @ Propagated L' mark # b = trail (cons_trail (Propagated L (C + {#L#})) S)"
      hence "(a=[] \<and> L = L' \<and> cls_of_mark mark = C + {#L#} \<and> b = trail S)
        \<or> tl a @ Propagated L' mark # b = trail S"
        by (cases a) fastforce+
      moreover {
        assume "tl a @ Propagated L' mark # b = trail S"
        hence "b \<Turnstile>as CNot (cls_of_mark mark - {#L'#}) \<and> L' \<in># cls_of_mark mark"
          using propagate.prems(6) by auto
      }
      moreover {
        assume "a=[]" and "L = L'" and "cls_of_mark mark = C + {#L#}" and "b = trail S"
        hence "b \<Turnstile>as CNot (cls_of_mark mark - {#L#}) \<and> L \<in># cls_of_mark mark"
          using \<open>trail S \<Turnstile>as CNot C\<close> by auto
      }
      ultimately show "b \<Turnstile>as CNot (cls_of_mark mark - {#L'#}) \<and> L' \<in># cls_of_mark mark" by blast
    qed
next
  case (decided L)
  have "\<And>a La mark b. a @ Propagated La mark # b = Marked L (backtrack_lvl S+1) # trail S
    \<Longrightarrow> tl a @ Propagated La mark # b = trail S" by (case_tac a, auto)
  thus ?case using decided.prems(6) unfolding decided.hyps(1) by fastforce
next
  case (skip L C' M D) note tr = this(1)
  show ?case
    proof (intro allI impI)
      fix L' mark a b
      assume "a @ Propagated L' mark # b = trail (tl_trail S)"
      hence "a @ Propagated L' mark # b = M" using tr by simp
      hence "(Propagated L C' # a) @ Propagated L' mark # b = Propagated L C' # M" by auto
      moreover have "\<forall>La mark a b. a @ Propagated La mark # b = Propagated L C' # M
        \<longrightarrow> b \<Turnstile>as CNot (cls_of_mark mark - {#La#}) \<and> La \<in># cls_of_mark mark"
        using skip.prems(6) unfolding skip.hyps(1) by simp
      ultimately show "b \<Turnstile>as CNot (cls_of_mark mark - {#L'#}) \<and> L' \<in># cls_of_mark mark" by blast
    qed
next
  case (conflict D)
  thus ?case by simp
next
  case (resolve L C M D)
  show ?case unfolding resolve.hyps(1) trail_conv
    proof (intro allI impI)
      fix  L' mark a b
      assume "a @ Propagated L' mark # b = trail
        (update_conflicting (C_Clause (remdups_mset (D + C)))
        (update_trail (tl (Propagated L (mark_of_cls (C + {#L#})) # M)) S))"
      hence "Propagated L (mark_of_cls (C + {#L#})) # M
        = (Propagated L (mark_of_cls (C + {#L#})) # a) @ Propagated L' mark # b"
        by auto
      thus "b \<Turnstile>as CNot (cls_of_mark mark - {#L'#}) \<and> L' \<in># cls_of_mark mark"
        using resolve.prems(6) unfolding resolve.hyps(1) trail_conv by presburger
    qed
next
  case restart
  thus ?case by auto
next
  case forget
  thus ?case by auto
next
  case (backtrack K i M1 M2 L D) note confl = this(3)
  have "\<forall>l \<in> set M2. \<not>is_marked l"
    using get_all_marked_decomposition_snd_not_marked backtrack.hyps(1) by blast
  obtain M0 where M: "trail S = M0 @ M2 @ Marked K (i + 1) # M1"
    using backtrack.hyps(1) by auto
  show ?case unfolding trail_conv
    proof (intro allI impI)
      fix La mark a b
      assume "a @ Propagated La mark # b = trail (update_trail
        (Propagated L (mark_of_cls (D + {#L#})) # M1)
        (add_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True S))))"
      hence "(a = [] \<and> Propagated La mark = Propagated L (mark_of_cls (D + {#L#})) \<and> b = M1)
        \<or> tl a @ Propagated La mark # b = M1"
        by (cases a, auto)
      moreover {
        assume A: "a = []" and
          P: "Propagated La mark = Propagated L (mark_of_cls (D + {#L#}))" and
          b: "b = M1"
        have "trail S \<Turnstile>as CNot D" using backtrack.prems(3) confl by auto
        hence vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of (trail S)"
          unfolding atms_of_def
          by (meson image_subsetI mem_set_mset_iff true_annots_CNot_all_atms_defined)
        have "backtrack S  (update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1)
           (add_cls (D + {#L#}) (update_backtrack_lvl i
           (update_conflicting C_True S))))"
           using backtrack.intros[of S] backtrack.hyps by auto
        hence vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of M1"
          using backtrack_atms_of_D_in_M1 backtrack.prems(2-4) by auto
        have "no_dup (trail S)" using backtrack.prems(4) by auto
        hence vars_in_M1: "\<forall>x \<in> atms_of D. x \<notin>
          atm_of ` lits_of (M0 @ M2 @ Marked K (i + 1) # [])"
          using vars_of_D distinct_atms_of_incl_not_in_other[of "M0 @ M2 @ Marked K (i + 1) # []" M1]
          unfolding M by auto
        have "M1 \<Turnstile>as CNot D"
          using vars_in_M1 true_annots_remove_if_notin_vars[of "M0 @ M2 @ Marked K (i + 1) # []" M1
            "CNot D"] \<open>trail S \<Turnstile>as CNot D\<close> unfolding M lits_of_def by simp
        hence "b \<Turnstile>as CNot (cls_of_mark mark - {#La#}) \<and> La \<in># cls_of_mark mark"
          using P b by auto
      }
      moreover {
        assume "tl a @ Propagated La mark # b = M1"
        then obtain c' where "c' @ Propagated La mark # b = trail S" unfolding M by auto
        hence "b \<Turnstile>as CNot (cls_of_mark mark - {#La#}) \<and> La \<in># cls_of_mark mark"
          using backtrack.prems(6) unfolding backtrack.hyps(1) trail_conv by blast
      }
      ultimately show "b \<Turnstile>as CNot (cls_of_mark mark - {#La#}) \<and> La \<in># cls_of_mark mark" by fast
    qed
qed

lemma cdcl_conflicting_is_false:
  assumes "cdcl S S'"
  and confl_inv: "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T"
  and M_lev: "cdcl_M_level_inv S"
  and "\<forall>L mark a b. a @ Propagated L mark # b = (trail S)
    \<longrightarrow> (b \<Turnstile>as CNot (cls_of_mark mark - {#L#}) \<and> L \<in># cls_of_mark mark)"
  and dist: "distinct_cdcl_state S"
  shows "\<forall>T. conflicting S' = C_Clause T \<longrightarrow> trail S' \<Turnstile>as CNot T"
  using assms(1)
proof (induct rule: cdcl_all_induct)
  case (skip L C' M D)
  hence "Propagated L C' # M \<Turnstile>as CNot D" using assms by auto
  moreover
    have "L \<notin># D"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence "- L \<in> lits_of M"
          using in_CNot_implies_uminus(2)[of D L "Propagated L C' # M"]
          \<open>Propagated L C' # M \<Turnstile>as CNot D\<close> by simp
        thus False
          by (metis assms(3) cdcl_M_level_inv_decomp(1) consistent_interp_def insert_iff
            lits_of_cons marked_lit.sel(2) skip.hyps(1))
      qed
  ultimately show ?case
    using skip.hyps(1-3) true_annots_CNot_lit_of_notin_skip unfolding cdcl_M_level_inv_def
     by fastforce
next
  case (resolve L C M D) note tr = this(1) and confl = this(2)
  show ?case unfolding trail_conv
    proof (intro allI impI)
      fix T
      have "tl (trail S) \<Turnstile>as CNot C" using tr assms(4) by fastforce
      moreover
        have "distinct_mset (D + {#- L#})" using confl dist
          unfolding distinct_cdcl_state_def by auto
        hence "-L \<notin># D" unfolding distinct_mset_def by auto
        have "M \<Turnstile>as CNot D"
          proof -
            have "Propagated L (mark_of_cls (C + {#L#})) # M \<Turnstile>as CNot D \<union> CNot {#- L#}"
              using confl tr confl_inv  by force
            thus ?thesis
              using M_lev \<open>- L \<notin># D\<close> tr true_annots_lit_of_notin_skip by force
          qed
      moreover assume "conflicting (update_conflicting (C_Clause (remdups_mset (D + C)))
        (tl_trail S)) = C_Clause T "
      ultimately
        show "trail (update_conflicting (C_Clause (remdups_mset (D + C))) (tl_trail S)) \<Turnstile>as CNot T"
        using tr by auto
    qed
qed (auto simp: assms(2))

lemma cdcl_conflicting_decomp:
  assumes "cdcl_conflicting S"
  shows "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T"
  and "\<forall>L mark a b. a @ Propagated L mark # b = (trail S)
    \<longrightarrow> (b \<Turnstile>as CNot (cls_of_mark mark - {#L#}) \<and> L \<in># cls_of_mark mark)"
  using assms unfolding cdcl_conflicting_def by blast+

lemma cdcl_conflicting_decomp2:
  assumes "cdcl_conflicting S" and "conflicting S = C_Clause T"
  shows "trail S \<Turnstile>as CNot T"
  using assms unfolding cdcl_conflicting_def by blast+

lemma cdcl_conflicting_decomp2':
  assumes
    "cdcl_conflicting S" and
    "conflicting S = C_Clause D"
  shows "trail S \<Turnstile>as CNot D"
  using assms unfolding cdcl_conflicting_def by auto

lemma cdcl_conflicting_S0_cdcl[simp]:
  "finite N \<Longrightarrow> cdcl_conflicting (init_state N)"
  unfolding cdcl_conflicting_def by auto

subsubsection \<open>Putting all the invariants together\<close>
lemma cdcl_all_inv:
  assumes cdcl: "cdcl S S'" and
  1: "all_decomposition_implies (init_clss S) (get_all_marked_decomposition (trail S))" and
  2: "cdcl_learned_clause S" and
  4: "cdcl_M_level_inv S" and
  5: "no_strange_atm S" and
  7: "distinct_cdcl_state S" and
  8: "cdcl_conflicting S"
  shows "all_decomposition_implies (init_clss S') (get_all_marked_decomposition (trail S'))"
  and "cdcl_learned_clause S'"
  and "cdcl_M_level_inv S'"
  and "no_strange_atm S'"
  and "distinct_cdcl_state S'"
  and "cdcl_conflicting S'"
proof -
  show S1: "all_decomposition_implies (init_clss S') (get_all_marked_decomposition (trail S'))"
    using cdcl_propagate_is_conclusion[OF cdcl 1 2 _ 4 5] 8 unfolding cdcl_conflicting_def by blast
  show S2: "cdcl_learned_clause S'" using cdcl_learned_clss[OF cdcl 2] .
  show S4: "cdcl_M_level_inv S'" using cdcl_consistent_inv[OF cdcl 4] .
  show S5: "no_strange_atm S'"  using  cdcl_no_strange_atm_inv[OF cdcl 5] .
  show S7: "distinct_cdcl_state S'" using distinct_cdcl_state_inv[OF cdcl 7] .
  show S8: "cdcl_conflicting S'"
    using cdcl_conflicting_is_false[OF cdcl _ 4 _ 7]  8 cdcl_propagate_is_false[OF cdcl 1 2 _ 4 5
      _]
    unfolding cdcl_conflicting_def by fast
qed

lemma rtranclp_cdcl_all_inv:
  assumes
    cdcl: "rtranclp cdcl S S'" and
    1: "all_decomposition_implies (init_clss S) (get_all_marked_decomposition (trail S))" and
    2: "cdcl_learned_clause S" and
    4: "cdcl_M_level_inv S" and
    5: "no_strange_atm S" and
    7: "distinct_cdcl_state S" and
    8: "cdcl_conflicting S"
  shows
    "all_decomposition_implies (init_clss S') (get_all_marked_decomposition (trail S'))" and
    "cdcl_learned_clause S'" and
    "cdcl_M_level_inv S'" and
    "no_strange_atm S'" and
    "distinct_cdcl_state S'" and
    "cdcl_conflicting S'"
   using assms
proof (induct rule: rtranclp.induct)
  case (rtrancl_refl S)
    case 1 thus ?case by blast
    case 2 thus ?case by blast
    case 3 thus ?case by blast
    case 4 thus ?case by blast
    case 5 thus ?case by blast
    case 6 thus ?case by blast
next
  case (rtrancl_into_rtrancl S S' S'') note H = this
    case 1 with H(2-7)[OF this(1-6)] show ?case using cdcl_all_inv[OF H(8)]
        rtrancl_into_rtrancl.hyps(1) by presburger
    case 2 with H(2-7)[OF this(1-6)] show ?case using cdcl_all_inv[OF H(8)]
        rtrancl_into_rtrancl.hyps(1) by presburger
    case 3 with H(2-7)[OF this(1-6)] show ?case using cdcl_all_inv[OF H(8)]
        rtrancl_into_rtrancl.hyps(1) by presburger
    case 4 with H(2-7)[OF this(1-6)] show ?case using cdcl_all_inv[OF H(8)]
        rtrancl_into_rtrancl.hyps(1) by presburger
    case 5 with H(2-7)[OF this(1-6)] show ?case using cdcl_all_inv[OF H(8)]
        rtrancl_into_rtrancl.hyps(1) by presburger
    case 6 with H(2-7)[OF this(1-6)] show ?case using cdcl_all_inv[OF H(8)]
        rtrancl_into_rtrancl.hyps(1) by presburger
qed

lemma all_invariant_S0_cdcl:
  assumes "distinct_mset_set N" and "finite N"
  shows "all_decomposition_implies (init_clss (init_state N))
                                   (get_all_marked_decomposition (trail (init_state N)))"
  and "cdcl_learned_clause (init_state N)"
  and "\<forall>T. conflicting (init_state N) = C_Clause T \<longrightarrow> (trail (init_state N))\<Turnstile>as CNot T"
  and "no_strange_atm (init_state N)"
  and "consistent_interp (lits_of (trail (init_state N)))"
  and "\<forall>L mark a b. a @ Propagated L mark # b =  trail (init_state N) \<longrightarrow>
     (b \<Turnstile>as CNot (cls_of_mark mark - {#L#}) \<and> L \<in># cls_of_mark mark)"
  and "distinct_cdcl_state (init_state N)"
  and "\<forall>T. conflicting (init_state N) = C_Clause T \<longrightarrow> atms_of T \<subseteq> atm_of ` lits_of (fst (S0_cdcl N))"
  using assms by auto

(*prop 2.10.5.5*)
lemma cdcl_only_propagated_vars_unsat:
  assumes
    marked: "\<forall>x \<in> set M. \<not> is_marked x" and
    DN: "D \<in> N \<union> U" and
    D: "M \<Turnstile>as CNot D" and
    inv: "all_decomposition_implies N (get_all_marked_decomposition M)" and
    state: "state S = (M, N, U, k, C)" and
    learned_cl: "cdcl_learned_clause S" and
    atm_incl: "no_strange_atm S"
  shows "unsatisfiable N"
proof (rule ccontr)
  assume "\<not> unsatisfiable N"
  then obtain I where
    I: "I \<Turnstile>s N" and
    cons: "consistent_interp I" and
    tot: "total_over_m I N"
    unfolding satisfiable_def by auto
  have "atms_of_m N \<union> atms_of_m U = atms_of_m N"
    using atm_incl state unfolding total_over_m_def no_strange_atm_def
     by (auto simp add: st_equal clauses_def)
  hence "total_over_m I (N \<union> U)" using tot unfolding total_over_m_def by auto
  moreover have "N \<Turnstile>ps U" using learned_cl state unfolding cdcl_learned_clause_def by auto
  ultimately have I_D: "I \<Turnstile> D"
    using I DN cons unfolding true_clss_clss_def true_clss_def Ball_def by blast

  have l0: "{{#lit_of L#} |L. is_marked L \<and> L \<in> set M} = {}" using marked by auto
  have "atms_of_m (N \<union> (\<lambda>a. {#lit_of a#}) ` set M) = atms_of_m N"
    using atm_incl state unfolding no_strange_atm_def by auto
  hence "total_over_m I (N \<union> (\<lambda>a. {#lit_of a#}) ` (set M))"
    using tot unfolding total_over_m_def by auto
  hence "I \<Turnstile>s (\<lambda>a. {#lit_of a#}) ` (set M)"
    using all_decomposition_implies_propagated_lits_are_implied[OF inv] cons I
    unfolding true_clss_clss_def l0 by auto
  hence IM: "I \<Turnstile>s (\<lambda>a. {#lit_of a#}) ` set M" by auto
  {
    fix K
    assume "K \<in># D"
    hence "-K \<in> lits_of M"
      using D unfolding true_annots_def Ball_def CNot_def true_annot_def true_cls_def true_lit_def
      Bex_mset_def by (metis (mono_tags, lifting) count_single less_not_refl mem_Collect_eq)
    hence " -K \<in> I" using IM true_clss_singleton_lit_of_implies_incl lits_of_def by fastforce
  }
  hence "\<not> I \<Turnstile> D" using cons unfolding true_cls_def true_lit_def consistent_interp_def by auto
  thus False using I_D by blast
qed

(*prop 2.10.5.4*)
text \<open>We have actually a much stronger theorem, namely
  @{thm all_decomposition_implies_propagated_lits_are_implied}, that show that the only choices
  we made are marked in the formula\<close>
lemma
  assumes "all_decomposition_implies N (get_all_marked_decomposition M)"
  and "\<forall>m \<in> set M. \<not>is_marked m"
  shows "N \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set M"
proof -
  have T: "{{#lit_of L#} |L. is_marked L \<and> L \<in> set M} = {}" using assms(2) by auto
  thus ?thesis
    using all_decomposition_implies_propagated_lits_are_implied[OF assms(1)] unfolding T by simp
qed

(*prop 2.10.5.6*)
lemma conflict_with_false_implies_unsat:
  assumes
    cdcl: "cdcl S S'" and
    [simp]: "finite (init_clss S)" and
    "conflicting S' = C_Clause {#}" and
    learned: "cdcl_learned_clause S"
  shows "unsatisfiable (init_clss S)"
  using assms
proof -
  have "cdcl_learned_clause S'" using cdcl_learned_clss cdcl learned by auto
  hence "init_clss S' \<Turnstile>p {#}" using assms(3) unfolding cdcl_learned_clause_def by auto
  hence "init_clss S \<Turnstile>p {#}"
    using cdcl_init_clss[OF assms(1)] by auto
  thus ?thesis unfolding satisfiable_def true_clss_cls_def by auto
qed

lemma conflict_with_false_implies_terminated:
  assumes "cdcl S S'"
  and "conflicting S = C_Clause {#}"
  shows "False"
  using assms by (induct rule: cdcl_all_induct) auto

subsubsection \<open>No tautology is learned\<close>

lemma learned_clss_are_not_tautologies:
  assumes "cdcl S S'"
  and "\<forall>s \<in> learned_clss S. \<not>tautology s"
  and "cdcl_conflicting S"
  and "cdcl_M_level_inv S"
  shows "\<forall>s \<in> learned_clss S'. \<not>tautology s"
  using assms
proof (induct rule: cdcl_all_induct)
  case (backtrack K i M1 M2 L D) note confl = this(3) and  conflicting = this(7) and lev_inv = this(8)
  have "consistent_interp (lits_of (trail S))" using lev_inv by auto
  moreover
    have "trail S \<Turnstile>as CNot (D + {#L#})"
      using backtrack.prems(2) confl unfolding cdcl_conflicting_def by auto
    hence "lits_of (trail S) \<Turnstile>s CNot (D + {#L#})" using true_annots_true_cls by blast
  ultimately have "\<not>tautology (D + {#L#})" using consistent_CNot_not_tautology by blast
  thus ?case using backtrack by simp
qed auto

(*TODO this is wrong (in the sense that it is too general)*)
definition "final_cdcl_state (S:: 'st)
  \<longleftrightarrow> (trail S \<Turnstile>as init_clss S
    \<or> ((\<forall>L \<in> set (trail S). \<not>is_marked L) \<and>
       (\<exists>C \<in> init_clss S. trail S \<Turnstile>as CNot C)))"

definition "termination_cdcl_state (S:: 'st)
   \<longleftrightarrow> (trail S \<Turnstile>as init_clss S
     \<or> ((\<forall>L \<in> atms_of_m (init_clss S). L \<in> atm_of ` lits_of (trail S))
        \<and> (\<exists>C \<in> init_clss S. trail S \<Turnstile>as CNot C)))"

(* subsection \<open>CDCL Strong Completeness\<close>
fun mapi :: "('a \<Rightarrow> nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"mapi _ _ [] = []" |
"mapi f n (x # xs) = f x n # mapi f (n - 1) xs"

lemma mark_not_in_set_mapi[simp]: "L \<notin> set M \<Longrightarrow> Marked L k \<notin> set (mapi Marked i M)"
  by (induct M arbitrary: i) auto

lemma propagated_not_in_set_mapi[simp]: "L \<notin> set M \<Longrightarrow> Propagated L k \<notin> set (mapi Marked i M)"
  by (induct M arbitrary: i) auto

lemma cdcl_can_do_step:
  assumes
    "consistent_interp (set M)" and
    "distinct M" and
    "atm_of ` (set M) \<subseteq> atms_of_m N" and
    [simp]: "finite N" and
    "state S = (mapi Marked (length M) M, N, {}, length M, C_True)"
  shows "rtranclp cdcl (init_state N) S"
  using assms
proof (induct M)
  case Nil
  hence "S = init_state N"
    by (auto simp: st_equal)
  thus ?case  by auto
next
  case (Cons L M)
  let ?S' = "cons_trail (Marked L (length (L#M))) (incr_lvl S)"
  have "undefined_lit L (mapi Marked (length M) M)"
    using Cons.prems(1,2) unfolding defined_lit_def consistent_interp_def by fastforce
  moreover have "clauses S = N"
    using assms(5) clauses_def by blast
  moreover have "atm_of L \<in> atms_of_m N" using Cons.prems(3) by auto
  ultimately have "cdcl S ?S'" using cdcl.other[OF cdcl_o.decided[OF deciding[OF Cons(6), of L]]]
  Cons(6) by auto
  moreover have "consistent_interp (set M)" and "distinct M" and "atm_of ` set M \<subseteq> atms_of_m N"
    using Cons.prems(1-3) unfolding consistent_interp_def by auto
  ultimately show ?case using Cons.hyps(1) by aut o
qed

lemma cdcl_strong_completeness:
  assumes "set M \<Turnstile>s N"
  and "consistent_interp (set M)"
  and "distinct M"
  and "atm_of ` (set M) \<subseteq> atms_of_m N"
  shows "rtranclp cdcl (init_state N) (mapi Marked (length M) M, N, {}, length M, C_True)"
  and "final_cdcl_state (mapi Marked (length M) M, N, {}, length M, C_True)"
proof -
  show "rtranclp cdcl (S0_cdcl N) (mapi Marked (length M) M, N, {}, length M, C_True)"
    using cdcl_can_do_step assms by auto
  have "lits_of (mapi Marked (length M) M) = set M"
    by (induct M, auto)
  hence "mapi Marked (length M) M \<Turnstile>as N" using assms(1) true_annots_true_cls by metis
  thus "final_cdcl_state (mapi Marked (length M) M, N, {}, length M, C_True)"
    unfolding final_cdcl_state_def by auto
qed *)

subsection \<open>Higher level strategy\<close>
subsubsection \<open>Definition\<close>

lemma tranclp_conflict_iff[iff]:
  "full conflict S S' \<longleftrightarrow> (((\<forall>S''. \<not>conflict S' S'') \<and> conflict S S'))"
proof -
  have "tranclp conflict S S' \<Longrightarrow> conflict S S'"
    unfolding full_def by (induct rule: tranclp.induct) force+
  hence "tranclp conflict S S' \<Longrightarrow> conflict S S'" by (meson rtranclpD)
  thus ?thesis unfolding full_def by (meson tranclp.r_into_trancl)
qed

inductive cdcl_cp :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
conflict'[intro]: "conflict S S' \<Longrightarrow> cdcl_cp S S'" |
propagate': "propagate S S' \<Longrightarrow> cdcl_cp S S'"

lemma no_conflict_after_conflict:
  "conflict S T \<Longrightarrow> \<not>conflict T U"
  by (auto elim!: conflictE)

lemma no_propagate_after_conflict:
  "conflict S T \<Longrightarrow> \<not>propagate T U"
  by (auto elim!: conflictE)

lemma rtranclp_cdcl_cp_propagate_with_conflict_or_not:
  assumes "cdcl_cp\<^sup>+\<^sup>+ S U"
  shows "(propagate\<^sup>+\<^sup>+ S U \<and> conflicting U = C_True)
    \<or> (\<exists>T D. propagate\<^sup>*\<^sup>* S T \<and> conflict T U \<and> conflicting U = C_Clause D)"
proof -
  have "propagate\<^sup>+\<^sup>+ S U \<or> (\<exists>T. propagate\<^sup>*\<^sup>* S T \<and> conflict T U)"
    using assms by induction
    (auto simp: cdcl_cp.simps tranclp_into_rtranclp
          dest:no_conflict_after_conflict no_propagate_after_conflict)
  moreover
    have "propagate\<^sup>+\<^sup>+ S U \<Longrightarrow> conflicting U = C_True"
      unfolding tranclp_unfold_end by auto
  moreover
    have "\<And>T. conflict T U \<Longrightarrow> \<exists>D. conflicting U = C_Clause D"
      by auto
  ultimately show ?thesis by auto
qed

lemma cdcl_cp_conflicting_not_empty[simp]: "conflicting S = C_Clause D  \<Longrightarrow> \<not>cdcl_cp S S'"
proof
  assume "cdcl_cp S S'" and "conflicting S = C_Clause D"
  thus False by (induct rule: cdcl_cp.induct) auto
qed

lemma no_step_cdcl_cp_no_conflict_no_propagate:
  assumes "no_step cdcl_cp S"
  shows "no_step conflict S" and "no_step propagate S"
  using assms conflict' apply blast
  by (meson assms conflict' propagate')

text \<open>CDCL with the reasonable strategy: we fully propagate the conflict and propagate, then we
  apply any other possible rule @{term "cdcl_o S S'"} and re-apply conflict and propagate
  @{term "full0 cdcl_cp S' S''"}\<close>
inductive cdcl_s :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
conflict': "full cdcl_cp S S' \<Longrightarrow> cdcl_s S S'" |
other': "cdcl_o S S'  \<Longrightarrow> no_step cdcl_cp S \<Longrightarrow> full0 cdcl_cp S' S'' \<Longrightarrow> cdcl_s S S''"

subsubsection \<open>Invariants\<close>
text \<open>These are the same invariants as before, but lifted\<close>
lemma cdcl_cp_learned_clause_inv:
  assumes "cdcl_cp S S'"
  shows "learned_clss S = learned_clss S'"
  using assms by (induct rule: cdcl_cp.induct) fastforce+

lemma rtranclp_cdcl_cp_learned_clause_inv:
  assumes "cdcl_cp\<^sup>*\<^sup>* S S'"
  shows "learned_clss S = learned_clss S'"
  using assms by (induct rule: rtranclp.induct) (fastforce dest: cdcl_cp_learned_clause_inv)+

lemma tranclp_cdcl_cp_learned_clause_inv:
  assumes "cdcl_cp\<^sup>+\<^sup>+ S S'"
  shows "learned_clss S = learned_clss S'"
  using assms by (simp add: rtranclp_cdcl_cp_learned_clause_inv tranclp_into_rtranclp)

lemma cdcl_cp_backtrack_lvl:
  assumes "cdcl_cp S S'"
  shows "backtrack_lvl S = backtrack_lvl S'"
  using assms by (induct rule: cdcl_cp.induct) fastforce+

lemma rtranclp_cdcl_cp_backtrack_lvl:
  assumes "cdcl_cp\<^sup>*\<^sup>* S S'"
  shows "backtrack_lvl S = backtrack_lvl S'"
  using assms by (induct rule: rtranclp.induct) (fastforce dest: cdcl_cp_backtrack_lvl)+

lemma cdcl_cp_consistent_inv:
  assumes "cdcl_cp S S'"
  and "cdcl_M_level_inv S"
  shows "cdcl_M_level_inv S'"
  using assms
proof (induct rule: cdcl_cp.induct)
  case (conflict')
  thus ?case using cdcl_consistent_inv cdcl.conflict by blast
next
  case (propagate' S S')
  have "cdcl S S'"
    using propagate'.hyps(1) propagate by blast
  thus "cdcl_M_level_inv S'"
    using propagate'.prems(1)  cdcl_consistent_inv propagate by blast
qed

lemma full_cdcl_cp_consistent_inv:
  assumes "full cdcl_cp S S'"
  and "cdcl_M_level_inv S"
  shows "cdcl_M_level_inv S'"
  using assms unfolding full_def
proof -
  have "cdcl_cp\<^sup>+\<^sup>+ S S'" and "cdcl_M_level_inv S" using assms unfolding full_def by auto
  thus ?thesis by (induct rule: tranclp.induct) (blast intro: cdcl_cp_consistent_inv)+
qed

lemma rtranclp_cdcl_cp_consistent_inv:
  assumes "rtranclp cdcl_cp S S'"
  and "cdcl_M_level_inv S"
  shows "cdcl_M_level_inv S'"
  using assms unfolding full_def
  by (induction rule: rtranclp_induct) (blast intro: cdcl_cp_consistent_inv)+

lemma cdcl_s_consistent_inv:
  assumes "cdcl_s S S'"
  and "cdcl_M_level_inv S"
  shows "cdcl_M_level_inv S'"
  using assms apply (induct rule: cdcl_s.induct)
  unfolding full0_unfold by (blast intro: cdcl_consistent_inv full_cdcl_cp_consistent_inv cdcl.other)+

lemma rtranclp_cdcl_s_consistent_inv:
  assumes "cdcl_s\<^sup>*\<^sup>* S S'"
  and "cdcl_M_level_inv S"
  shows "cdcl_M_level_inv S'"
  using assms by (induction) (auto dest!: cdcl_s_consistent_inv)

lemma cdcl_o_no_more_init_clss:
  assumes "cdcl_o S S'"
  shows "init_clss S = init_clss S'"
  using assms by (induct rule: cdcl_o_induct) auto

lemma tranclp_cdcl_o_no_more_init_clss:
  assumes "cdcl_o\<^sup>+\<^sup>+ S S'"
  shows "init_clss S = init_clss S'"
  using assms by (induct rule: tranclp.induct) (auto dest: cdcl_o_no_more_init_clss)

lemma rtranclp_cdcl_o_no_more_init_clss:
  assumes "cdcl_o\<^sup>*\<^sup>* S S'"
  shows "init_clss S = init_clss S'"
  using assms by (induct rule: rtranclp.induct) (auto dest: cdcl_o_no_more_init_clss)

lemma cdcl_cp_no_more_init_clss:
  assumes "cdcl_cp S S'"
  shows "init_clss S = init_clss S'"
  using assms by (induct rule: cdcl_cp.induct) auto

lemma tranclp_cdcl_cp_no_more_init_clss:
  assumes "cdcl_cp\<^sup>+\<^sup>+ S S'"
  shows "init_clss S = init_clss S'"
  using assms by (induct rule: tranclp.induct) (auto dest: cdcl_cp_no_more_init_clss)

lemma cdcl_s_no_more_init_clss:
  assumes "cdcl_s S S'"
  shows "init_clss S = init_clss S'"
  using assms
  apply (induct rule: cdcl_s.induct)
  unfolding full_def full0_def apply (blast dest: tranclp_cdcl_cp_no_more_init_clss
    tranclp_cdcl_o_no_more_init_clss)
  by (metis cdcl_o_no_more_init_clss rtranclp_unfold tranclp_cdcl_cp_no_more_init_clss)

lemma rtranclp_cdcl_s_no_more_init_clss:
  assumes "cdcl_s\<^sup>*\<^sup>* S S'"
  shows "init_clss S = init_clss S'"
  using assms
  apply (induct rule: rtranclp.induct, simp)
  using cdcl_s_no_more_init_clss by fast


lemma cdcl_cp_dropWhile_trail':
  assumes "cdcl_cp S S'"
  obtains M where "trail S' = M @ trail S" and " (\<forall>l \<in> set M. \<not>is_marked l)"
  using assms by (induction) fastforce+

lemma rtranclp_cdcl_cp_dropWhile_trail':
  assumes "cdcl_cp\<^sup>*\<^sup>* S S'"
  obtains M :: "('v, nat, 'mark) marked_lit list" where
    "trail S' = M @ trail S" and "\<forall>l \<in> set M. \<not>is_marked l"
  using assms by (induction) (fastforce dest!: cdcl_cp_dropWhile_trail')+

lemma cdcl_cp_dropWhile_trail:
  assumes "cdcl_cp S S'"
  shows "\<exists>M. trail S' = M @ trail S \<and> (\<forall>l \<in> set M. \<not>is_marked l)"
  using assms by (induction) fastforce+

lemma rtranclp_cdcl_cp_dropWhile_trail:
  assumes "cdcl_cp\<^sup>*\<^sup>* S S'"
  shows "\<exists>M. trail S' = M @ trail S \<and> (\<forall>l \<in> set M. \<not>is_marked l)"
  using assms by (induction) (fastforce dest: cdcl_cp_dropWhile_trail)+

text \<open>This theorem can be seen a a termination theorem for @{term cdcl_cp}.\<close>
(* TODO Move wf here *)
lemma always_exists_full_cdcl_cp_step:
  assumes "finite (init_clss S)"
  and "no_strange_atm S"
  shows "\<exists>S''. full0 cdcl_cp S S''"
  using assms
proof (induct "card (atms_of_m (init_clss S) - atm_of `lits_of (trail S))" arbitrary: S)
  case 0 note card = this(1) and finite = this(2) and alien = this(3)
  hence atm: "atms_of_m (init_clss S) = atm_of ` lits_of (trail S)"
    unfolding no_strange_atm_def by (metis (no_types, lifting) atms_of_m_finite card_Diff_subset
      card_seteq diff_is_0_eq finite_subset)
  { assume a: "\<exists>S'. conflict S S'"
    then obtain S' where S': "conflict S S'" by metis
    hence "\<forall>S''. \<not>cdcl_cp S' S''" by auto
    hence ?case using a S' cdcl_cp.conflict' unfolding full0_def by blast
  }
  moreover {
    assume a: "\<exists>S'. propagate S S'"
    then obtain S' where "propagate S S'" by blast
    then obtain M N U k C L where S: "state S = (M, N, U, k, C_True)"
    and S': "state S' = (Propagated L (mark_of_cls (C + {#L#})) # M, N, U, k, C_True)"
    and "C + {#L#} \<in> clauses S"
    and "M \<Turnstile>as CNot C"
    and "undefined_lit L M"
    using propagate by auto
    have "atms_of_m U \<subseteq> atms_of_m N" using alien S unfolding no_strange_atm_def by auto
    hence "atm_of L \<in> atms_of_m (init_clss S)"
      using \<open>C + {#L#} \<in> clauses S\<close> S  unfolding atms_of_m_def clauses_def by fastforce
    hence False using \<open>undefined_lit L M\<close> S unfolding atm unfolding lits_of_def
      by (auto simp add: defined_lit_map)
  }
  ultimately show ?case by (metis cdcl_cp.cases full0_def rtranclp.rtrancl_refl)
next
  case (Suc n) note IH = this(1) and card = this(2) and finite = this(3) and alien = this(4)
  { assume a: "\<exists>S'. conflict S S'"
    then obtain S' where S': "conflict S S'" by metis
    hence "\<forall>S''. \<not>cdcl_cp S' S''" by auto
    hence ?case  unfolding full0_def Ex_def using S' cdcl_cp.conflict' by blast
  }
  moreover {
    assume a: "\<exists>S'. propagate S S'"
    then obtain S' where propagate: "propagate S S'" by blast
    then obtain M N U k C L where
      S: "state S = (M, N, U, k, C_True)" and
      S': "state S' = (Propagated L (mark_of_cls (C + {#L#})) # M, N, U, k, C_True)" and
      "C + {#L#} \<in> clauses S" and
      "M \<Turnstile>as CNot C" and
      "undefined_lit L M"
      by (auto elim!: propagateE)
    hence "atm_of L \<notin> atm_of ` lits_of M" unfolding lits_of_def by (auto simp add: defined_lit_map)
    moreover
      have "no_strange_atm S'" using alien propagate
        by (meson cdcl.propagate cdcl_no_strange_atm_inv)
      hence "atm_of L \<in> atms_of_m N" using S' unfolding no_strange_atm_def by auto
      hence "\<And>A. {atm_of L} \<subseteq> atms_of_m N - A \<or> atm_of L \<in> A" by force
    moreover have "Suc n - card {atm_of L} = n" by simp
    moreover have "card (atms_of_m N - atm_of ` lits_of M) = Suc n"
     using card S S' by simp
    ultimately
      have "card (atms_of_m N - atm_of ` insert L (lits_of M)) = n"
        by (metis (no_types) Diff_insert card_Diff_subset finite.emptyI finite.insertI image_insert)
      hence "n = card (atms_of_m (init_clss S') - atm_of ` lits_of (trail S'))"
        using card S S' by simp

    moreover have "finite (init_clss S')" using finite S S' by auto
    ultimately have a1: "Ex (full0 cdcl_cp S')" using IH \<open>no_strange_atm S'\<close> by blast
    have ?case
      proof -
        obtain S'' :: "'st" where
          ff1: "cdcl_cp\<^sup>*\<^sup>* S' S'' \<and> no_step cdcl_cp S''"
          using a1 unfolding full0_def by blast
        have "cdcl_cp\<^sup>*\<^sup>* S S''"
          using ff1 cdcl_cp.intros(2)[OF propagate]
          by (metis (no_types) converse_rtranclp_into_rtranclp)
        hence "\<exists>S''. cdcl_cp\<^sup>*\<^sup>* S S'' \<and> (\<forall>S'''. \<not> cdcl_cp S'' S''')"
          using ff1 by blast
        thus ?thesis unfolding full0_def
          by meson
      qed

    }
  ultimately show ?case unfolding full0_def by (metis cdcl_cp.cases rtranclp.rtrancl_refl)
qed

subsubsection \<open>Literal of highest level in conflicting init_clss\<close>
text \<open>One important property of the cdcl with strategy is that, whenever a conflict takes place,
  there is at least a literal of level k involved (except if we have derived the false clause).
  The reason is that we apply conflicts as soon as possible\<close>
abbreviation no_clause_is_false :: "'st \<Rightarrow> bool" where
"no_clause_is_false \<equiv>
  \<lambda>S. (conflicting S = C_True \<longrightarrow> (\<forall>D \<in> clauses S. \<not>trail S \<Turnstile>as CNot D))"

abbreviation conflict_is_false_with_level :: "'st \<Rightarrow> bool" where
"conflict_is_false_with_level S' \<equiv> \<forall>D. conflicting S' = C_Clause D \<longrightarrow> D \<noteq> {#}
  \<longrightarrow> (\<exists>L \<in># D. get_level L (trail S') = backtrack_lvl S')"

lemma not_conflict_not_any_negated_init_clss:
  assumes "\<forall> S'. \<not>conflict S S'"
  shows "no_clause_is_false S"
  using assms by (fastforce simp add: conflict.simps)

lemma full0_cdcl_cp_not_any_negated_init_clss:
  assumes "full0 cdcl_cp S S'"
  shows "no_clause_is_false S'"
  using assms not_conflict_not_any_negated_init_clss unfolding full0_def by blast

lemma full_cdcl_cp_not_any_negated_init_clss:
  assumes "full cdcl_cp S S'"
  shows "no_clause_is_false S'"
  using assms not_conflict_not_any_negated_init_clss unfolding full_def by blast

lemma cdcl_s_not_non_negated_init_clss:
  assumes "cdcl_s S S'"
  shows "no_clause_is_false S'"
  using assms apply (induct rule: cdcl_s.induct)
  using full_cdcl_cp_not_any_negated_init_clss full0_cdcl_cp_not_any_negated_init_clss by metis+

lemma cdcl_s_conflict_ex_lit_of_max_level:
  assumes "cdcl_cp S S'"
  and "no_clause_is_false S"
  and "cdcl_M_level_inv S"
  shows "conflict_is_false_with_level S'"
  using assms
proof (induct rule: cdcl_cp.induct)
  case conflict'
  thus ?case by auto
next
  case propagate'
  thus ?case by auto
qed

lemma no_chained_conflict:
  assumes "conflict S S'"
  and "conflict S' S''"
  shows False
  using assms by (auto elim!: conflictE)

lemma rtranclp_cdcl_cp_propa_or_propa_confl:
  assumes "cdcl_cp\<^sup>*\<^sup>* S U"
  shows "propagate\<^sup>*\<^sup>* S U \<or> (\<exists>T. propagate\<^sup>*\<^sup>* S T  \<and> conflict T U)"
  using assms
proof (induction)
  case base
  thus ?case by auto
next
  case (step U V) note SU = this(1) and UV = this(2) and IH = this(3)
  consider (confl) T where "propagate\<^sup>*\<^sup>* S T" and "conflict T U"
    | (propa) "propagate\<^sup>*\<^sup>* S U" using IH by auto
  thus ?case
    proof cases
      case confl
      hence False using UV by auto
      thus ?thesis by fast
    next
      case propa
      also have "conflict U V \<or> propagate U V" using UV by (auto simp add: cdcl_cp.simps)
      ultimately show ?thesis by auto
    qed
qed

lemma get_level_skip_beginning_hd_get_all_levels_of_marked:
  assumes "atm_of L \<notin> atm_of ` lits_of S"
  and "get_all_levels_of_marked S \<noteq> []"
  shows "get_level L (M@ S) = get_rev_level L (hd (get_all_levels_of_marked S)) (rev M)"
  using assms
proof (induction S arbitrary: M rule: marked_lit_list_induct)
  case nil
  thus ?case by (auto simp add: lits_of_def)
next
  case (marked K m) note notin = this(2)
  thus ?case by (auto simp add: lits_of_def)
next
  case (proped L l) note IH = this(1) and L = this(2) and neq = this(3)
  show ?case using IH[of "M@[Propagated L l]"] L neq by (auto simp add: atm_of_eq_atm_of)
qed

lemma get_level_skip_beginning_not_marked_rev:
  assumes "atm_of L \<notin> atm_of ` lit_of `(set S)"
  and "\<forall>s\<in>set S. \<not>is_marked s"
  shows "get_level L (M @ rev S) = get_level L M"
  using assms by (induction S rule: marked_lit_list_induct) auto

lemma get_level_skip_beginning_not_marked[simp]:
  assumes "atm_of L \<notin> atm_of ` lit_of `(set S)"
  and "\<forall>s\<in>set S. \<not>is_marked s"
  shows "get_level L (M @ S) = get_level L M"
  using get_level_skip_beginning_not_marked_rev[of L "rev S" M] assms by auto

lemma get_rev_level_skip_beginning_not_marked[simp]:
  assumes "atm_of L \<notin> atm_of ` lit_of `(set S)"
  and "\<forall>s\<in>set S. \<not>is_marked s"
  shows "get_rev_level L 0 (rev S @ rev M) = get_level L M"
  using get_level_skip_beginning_not_marked_rev[of L "rev S" M] assms by auto

lemma get_all_levels_of_marked_nil_iff_not_is_marked:
  "get_all_levels_of_marked xs = [] \<longleftrightarrow> (\<forall> x \<in> set xs. \<not>is_marked x)"
  using assms by (induction xs rule: marked_lit_list_induct) auto

lemma get_level_skip_all_not_marked[simp]:
  fixes M
  defines "M' \<equiv> rev M"
  assumes "\<forall>m\<in>set M. \<not> is_marked m"
  shows "get_level L M = 0"
proof -
  have M: "M = rev M'"
    unfolding M'_def by auto
  show ?thesis
    using assms unfolding M by (induction M' rule: marked_lit_list_induct) auto
qed

lemma get_level_skip_in_all_not_marked:
  fixes M :: "('a, nat, 'b) marked_lit list" and L :: "'a literal"
  assumes "\<forall>m\<in>set M. \<not> is_marked m"
  and "atm_of L \<in> atm_of ` lit_of ` (set M)"
  shows "get_rev_level L n M = n"
proof -
  show ?thesis
    using assms by (induction M rule: marked_lit_list_induct) auto
qed

thm wf_trancl
lemma rtranclp_cdcl_co_conflict_ex_lit_of_max_level:
  assumes full: "full0 cdcl_cp S U"
  and cls_f: "no_clause_is_false S"
  and "conflict_is_false_with_level S"
  and lev: "cdcl_M_level_inv S"
  shows "conflict_is_false_with_level U"
proof (intro allI impI)
  fix D
  assume confl: "conflicting U = C_Clause D" and
    D: "D \<noteq> {#}"
  consider (CT) "conflicting S = C_True" | (SD) D' where "conflicting S = C_Clause D'"
    by (cases "conflicting S") auto
  thus "\<exists>L\<in>#D. get_level L (trail U) = backtrack_lvl U"
    proof (cases)
      case SD
      hence "S = U"
        by (metis (no_types) assms(1) cdcl_cp_conflicting_not_empty full0_def rtranclpD tranclpD)
      thus  ?thesis using assms(3) confl D by blast-
    next
      case CT
      have "init_clss U = init_clss S" and "learned_clss U = learned_clss S"
        using assms(1) unfolding full0_def
          apply (metis (no_types) rtranclpD tranclp_cdcl_cp_no_more_init_clss)
        by (metis (mono_tags, lifting) assms(1) full0_def rtranclp_cdcl_cp_learned_clause_inv)
      obtain T where "propagate\<^sup>*\<^sup>* S T" and TU: "conflict T U"
        proof -
          have f5: "U \<noteq> S"
            using confl CT by force
          hence "cdcl_cp\<^sup>+\<^sup>+ S U"
            by (metis full full0_def rtranclpD)
          have "\<And>p pa. \<not> propagate p pa \<or> conflicting pa =
            (C_True::'v literal multiset conflicting_clause)"
            by auto
          thus ?thesis
            using f5 that rtranclp_cdcl_cp_propagate_with_conflict_or_not[OF \<open>cdcl_cp\<^sup>+\<^sup>+ S U\<close>]
            full confl CT unfolding full0_def by auto
        qed
      have "init_clss T = init_clss S" and "learned_clss T = learned_clss S"
        using TU \<open>init_clss U = init_clss S\<close> \<open>learned_clss U = learned_clss S\<close> by auto
      hence "D \<in> clauses S"
        using TU confl by (auto elim!: conflictE simp: clauses_def)
      hence  "\<not> trail S \<Turnstile>as CNot D"
        using cls_f CT by simp
      moreover
        obtain M where tr_U: "trail U = M @ trail S" and nm: "\<forall>m\<in>set M. \<not>is_marked m"
          by (metis (mono_tags, lifting) assms(1) full0_def rtranclp_cdcl_cp_dropWhile_trail)
        have "trail U \<Turnstile>as CNot D"
          using TU confl by auto
      ultimately obtain L where "L \<in># D" and "-L \<in> lits_of M"
        unfolding tr_U CNot_def true_annots_def Ball_def true_annot_def true_cls_def by auto

      moreover have inv_U: "cdcl_M_level_inv U"
        by (metis cdcl_s.conflict' cdcl_s_consistent_inv full full0_unfold lev)
      moreover
        have "backtrack_lvl U = backtrack_lvl S"
          using full unfolding full0_def by (auto dest: rtranclp_cdcl_cp_backtrack_lvl)

      moreover
        have "no_dup (trail U)"
          using inv_U unfolding cdcl_M_level_inv_def by auto
        hence LS: "atm_of L \<notin> atm_of ` lits_of (trail S)"
        (*TODO Factor proof*)
          using \<open>-L \<in> lits_of M\<close> unfolding tr_U lits_of_def
            apply (auto simp add: atm_of_eq_atm_of)
          using IntI empty_iff image_eqI apply (metis IntI atm_of_uminus empty_iff image_eqI)+
          done
      ultimately have "get_level L (trail U) = backtrack_lvl U"
        proof (cases "get_all_levels_of_marked (trail S) \<noteq> []", goal_cases)
          case 2 note LD = this(1) and LM = this(2) and inv_U = this(3) and US = this(4) and
            LS = this(5) and ne = this(6)
          have "backtrack_lvl S = 0"
            using lev ne unfolding cdcl_M_level_inv_def by auto
          moreover have "get_rev_level L 0 (rev M) = 0"
            using nm by auto
          ultimately show ?thesis using LS ne US unfolding tr_U
            by (simp add: get_all_levels_of_marked_nil_iff_not_is_marked lits_of_def)
        next
          case 1 note LD = this(1) and LM = this(2) and inv_U = this(3) and US = this(4) and
            LS = this(5) and ne = this(6)

          have "hd (get_all_levels_of_marked (trail S)) = backtrack_lvl S"
            using ne unfolding cdcl_M_level_inv_decomp(4)[OF lev] by auto
          moreover have "atm_of L \<in> atm_of ` lits_of M "
            using \<open>-L \<in> lits_of M\<close> by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
              lits_of_def)
          ultimately show ?thesis
            using nm ne unfolding tr_U
            using get_level_skip_beginning_hd_get_all_levels_of_marked[OF LS, of M]
               get_level_skip_in_all_not_marked[of "rev M" L "backtrack_lvl S"]
            unfolding lits_of_def US
            by auto
          qed
      thus "\<exists>L\<in>#D. get_level L (trail U) = backtrack_lvl U"
        using \<open>L \<in># D\<close> by blast
    qed
qed

subsubsection \<open>Literal of highest level in marked literals\<close>
definition mark_is_false_with_level :: "'st \<Rightarrow> bool" where
"mark_is_false_with_level S' \<equiv>
  \<forall>D M1 M2 L.  M1 @ Propagated L D # M2 = trail S' \<longrightarrow> cls_of_mark D - {#L#} \<noteq> {#}
    \<longrightarrow> (\<exists>L. L \<in># cls_of_mark D \<and> get_level L (trail S') = get_maximum_possible_level M1)"

definition no_more_propagation_to_do:: "'st \<Rightarrow> bool" where
"no_more_propagation_to_do S \<equiv>
  \<forall>D M M' L. D + {#L#} \<in> clauses S \<longrightarrow> trail S = M' @ M \<longrightarrow> M \<Turnstile>as CNot D
    \<longrightarrow> undefined_lit L M \<longrightarrow> get_maximum_possible_level M < backtrack_lvl S
    \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S) = get_maximum_possible_level M)"

lemma propagate_no_more_propagation_to_do:
  assumes propagate: "propagate S S'"
  and H: "no_more_propagation_to_do S"
  and M: "cdcl_M_level_inv S"
  shows "no_more_propagation_to_do S'"
  using assms
proof -
  obtain M N U k C L where
    S: "state S = (M, N, U, k, C_True)" and
    S': "state S' = (Propagated L (mark_of_cls (C + {#L#})) # M, N, U, k, C_True)" and
    "C + {#L#} \<in> clauses S" and
    "M \<Turnstile>as CNot C" and
    "undefined_lit L M"
    using propagate by auto
  let ?M' = "Propagated L (mark_of_cls (C + {#L#})) # M"
  show ?thesis unfolding no_more_propagation_to_do_def
    proof (intro allI impI)
      fix D M1 M2 L'
      assume D_L: "D + {#L'#} \<in> clauses S'"
      and "trail S' = M2 @ M1"
      and get_max: "get_maximum_possible_level M1 < backtrack_lvl S'"
      and "M1 \<Turnstile>as CNot D"
      and undef: "undefined_lit L' M1"
      have "tl M2 @ M1 = trail S \<or> (M2 = [] \<and> M1 = Propagated L (mark_of_cls (C + {#L#})) # M)"
        using \<open>trail S' = M2 @ M1\<close> S' S by (cases M2) auto
      moreover {
        assume "tl M2 @ M1 = trail S"
        moreover have "D + {#L'#} \<in> clauses S" using D_L S S' unfolding clauses_def by auto
        moreover have "get_maximum_possible_level M1 < backtrack_lvl S"
          using get_max S S' by auto
        ultimately obtain L' where "L' \<in># D" and
          "get_level L' (trail S) = get_maximum_possible_level M1"
          using H \<open>M1 \<Turnstile>as CNot D\<close> undef unfolding no_more_propagation_to_do_def by metis
        moreover
          { have "cdcl_M_level_inv S'"
              using cdcl_consistent_inv[OF _ M] cdcl.propagate[OF propagate] by blast
            hence "no_dup ?M'" using S' by auto
            moreover
              have "atm_of L' \<in> atm_of ` (lits_of M1)"
                using \<open>L' \<in># D\<close> \<open>M1 \<Turnstile>as CNot D\<close> by (metis atm_of_uminus image_eqI
                  in_CNot_implies_uminus(2))
              hence "atm_of L' \<in> atm_of ` (lits_of M)"
                using \<open>tl M2 @ M1 = trail S\<close> S by auto
            ultimately have "atm_of L \<noteq> atm_of L'" unfolding lits_of_def by auto
        }
        ultimately have "\<exists>L' \<in># D. get_level L' (trail S') = get_maximum_possible_level M1"
          using S S' by auto
      }
      moreover {
        assume "M2 = []" and M1: "M1 = Propagated L (mark_of_cls (C + {#L#})) # M"
        have "cdcl_M_level_inv S'"
          using cdcl_consistent_inv[OF _ M] cdcl.propagate[OF propagate] by blast
        hence "get_all_levels_of_marked (trail S') = rev ([Suc 0..<(Suc 0+k)])" using S' by auto
        hence "get_maximum_possible_level M1 = backtrack_lvl S'"
          using get_maximum_possible_level_max_get_all_levels_of_marked[of M1] S' M1
          by (auto intro: Max_eqI)
        hence False using get_max by auto
      }
      ultimately show "\<exists>L. L \<in># D \<and> get_level L (trail S') = get_maximum_possible_level M1" by fast
   qed
qed

lemma conflict_no_more_propagation_to_do:
  assumes conflict: "conflict S S'"
  and H: "no_more_propagation_to_do S"
  and M: "cdcl_M_level_inv S"
  shows "no_more_propagation_to_do S'"
  using assms unfolding no_more_propagation_to_do_def conflict.simps by force

lemma cdcl_cp_no_more_propagation_to_do:
  assumes conflict: "cdcl_cp S S'"
  and H: "no_more_propagation_to_do S"
  and M: "cdcl_M_level_inv S"
  shows "no_more_propagation_to_do S'"
  using assms
  proof (induct rule: cdcl_cp.induct)
  case (conflict' S S')
  thus ?case using conflict_no_more_propagation_to_do[of S S'] by blast
next
  case (propagate' S S') note S = this
  show 1: "no_more_propagation_to_do S'"
    using propagate_no_more_propagation_to_do[of S S']  S by blast
qed

lemma cdcl_then_exists_cdcl_s_step:
  assumes o: "cdcl_o S S'"
  and alien: "no_strange_atm S"
  and finite: "finite (init_clss S)"
  shows "\<exists>S'. cdcl_s S S'"
proof -
  obtain S'' where "full0 cdcl_cp S' S''"
    using always_exists_full_cdcl_cp_step alien cdcl_no_strange_atm_inv cdcl_o_no_more_init_clss
    local.finite o other by fastforce
  thus ?thesis
    using assms by (metis always_exists_full_cdcl_cp_step cdcl_s.conflict' full0_unfold other')
qed

(* TODO Move *)
lemma in_get_all_levels_of_marked_iff_decomp:
  "i \<in> set (get_all_levels_of_marked M) \<longleftrightarrow> (\<exists>c K c'. M = c @ Marked K i # c')" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?B
  thus ?A by auto
next
  assume ?A
  thus ?B
    apply (induction M rule: marked_lit_list_induct)
      apply auto[]
     apply (metis append_Cons append_Nil get_all_levels_of_marked.simps(2) set_ConsD)
    by (metis append_Cons get_all_levels_of_marked.simps(3))
qed

lemma backtrack_ex_decomp:
  assumes M_l: "cdcl_M_level_inv S"
  and i_S: "i < backtrack_lvl S"
  shows "\<exists>K M1 M2. (Marked K (i + 1) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))"
proof -
  let ?M = "trail S"
  have
    g: "get_all_levels_of_marked (trail S) = rev [Suc 0..<Suc (backtrack_lvl S)]"
    using M_l unfolding cdcl_M_level_inv_def by simp_all
  hence "i+1 \<in> set (get_all_levels_of_marked (trail S))"
    using i_S by auto

  then obtain c K c' where tr_S: "trail S = c @ Marked K (i + 1) # c'"
    using in_get_all_levels_of_marked_iff_decomp[of "i+1" "trail S"] by auto

  obtain M1 M2 where "(Marked K (i + 1) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))"
    unfolding tr_S apply (induct c rule: marked_lit_list_induct)
      apply auto[2]
    apply (case_tac "hd (get_all_marked_decomposition (xs @ Marked K (Suc i) # c'))")
    apply (case_tac "get_all_marked_decomposition (xs @ Marked K (Suc i) # c')")
    by auto
  thus ?thesis by blast
qed

lemma backtrack_no_decomp:
  assumes S: "state S = (M, N, U, k, C_Clause (D + {#L#}))"
  and L: "get_level L M = k"
  and D: "get_maximum_level D M < k"
  and M_L: "cdcl_M_level_inv S"
  shows "\<exists>S'. cdcl_o S S'"
proof -
  have L_D: "get_level L M = get_maximum_level (D + {#L#}) M"
    using L D by (simp add: get_maximum_level_plus)
  let ?i = "get_maximum_level D M"
  obtain K M1 M2 where K: "(Marked K (?i + 1) # M1, M2) \<in> set (get_all_marked_decomposition M)"
    using backtrack_ex_decomp[OF M_L, of ?i] D S by auto
  show ?thesis using backtracking[OF S K L L_D] by blast
qed

lemma cdcl_s_normal_forms:
  assumes termi: "\<forall>S'. \<not>cdcl_s S S'"
  and decomp: "all_decomposition_implies (init_clss S) (get_all_marked_decomposition (trail S))"
  and learned: "cdcl_learned_clause S"
  and level_inv: "cdcl_M_level_inv S"
  and alien: "no_strange_atm S"
  and no_dup: "distinct_cdcl_state S"
  and confl: "cdcl_conflicting S"
  and finite: "finite (init_clss S)"
  and confl_k: "conflict_is_false_with_level S"
  shows "(conflicting S = C_Clause {#} \<and> unsatisfiable (init_clss S))
         \<or> (conflicting S = C_True \<and> trail S \<Turnstile>as init_clss S)"
proof -
  let ?M = "trail S"
  let ?N = "init_clss S"
  let ?k = "backtrack_lvl S"
  let ?U = "learned_clss S"
  have "conflicting S = C_Clause {#}
        \<or> conflicting S = C_True
        \<or> (\<exists>D L. conflicting S = C_Clause (D + {#L#}))"
    apply (case_tac "conflicting S", auto)
    by (case_tac x2, auto)
  moreover {
    assume "conflicting S = C_Clause {#}"
    hence "unsatisfiable (init_clss S)"
      using assms(3) unfolding cdcl_learned_clause_def true_clss_cls_def
      by (metis (no_types, lifting) Un_insert_right atms_of_empty satisfiable_def
        sup_bot.right_neutral total_over_m_insert total_over_set_empty true_cls_empty)
  }
  moreover {
    assume "conflicting S = C_True"
    { assume "\<not>?M \<Turnstile>as ?N"
      have "atm_of ` (lits_of ?M) = atms_of_m ?N" (is "?A = ?B")
        proof
          show "?A \<subseteq> ?B" using alien unfolding no_strange_atm_def by auto
          show "?B \<subseteq> ?A"
            proof (rule ccontr)
              assume "\<not>?B \<subseteq> ?A"
              then obtain l where "l \<in> ?B" and "l \<notin> ?A" by auto
              hence "undefined_lit (Pos l) ?M"
                using \<open>l \<notin> ?A\<close> unfolding lits_of_def by (auto simp add: defined_lit_map)
              hence "\<exists>S'. cdcl_o S S'"
                using cdcl_o.decided decided.intros \<open>l \<in> ?B\<close> no_strange_atm_def
                by (metis \<open>conflicting S = C_True\<close> alien atms_of_m_union clauses_def literal.sel(1)
                  no_strange_atm_decomp(3) sup.orderE)
              thus False using termi cdcl_then_exists_cdcl_s_step[OF _ alien finite] by metis
            qed
          qed
        obtain D where "\<not> ?M \<Turnstile>a D" and "D \<in> ?N"
           using \<open>~?M \<Turnstile>as ?N\<close> unfolding lits_of_def true_annots_def Ball_def by auto
        have "atms_of D \<subseteq> atm_of ` (lits_of ?M)"
          using \<open>D \<in> ?N\<close> unfolding \<open>atm_of ` (lits_of ?M) = atms_of_m ?N\<close> atms_of_m_def
          by (auto simp add: atms_of_def)
        hence a1: "atm_of ` set_mset D \<subseteq> atm_of ` lits_of (trail S)"
          by (auto simp add: atms_of_def lits_of_def)
        have "?M \<Turnstile>as CNot D"
        (*TODO Try to find a better proof*)
          proof -
            { fix mm :: "'v clause"
              have ff1: "\<And>l la. (l::'a literal) \<noteq> la \<or> count {#l#} la = Suc 0"
                by simp
              have ff2: "\<And>a. a \<notin> atm_of ` set_mset D \<or> a \<in> atm_of ` lits_of (trail S)"
                using a1 by (meson subsetCE)
              have ff3: "\<And>l. l \<notin> lits_of (trail S) \<or> l \<notin># D"
                using \<open>\<not> ?M \<Turnstile>a D\<close> unfolding true_annot_def Ball_def lits_of_def true_cls_def
                Bex_mset_def by (meson true_lit_def)
              have ff4: "\<And>l. is_pos l \<or> Pos (atm_of l::'v) = - l"
                by (metis Neg_atm_of_iff uminus_Neg)
              have "\<And>l. is_neg l \<or> Neg (atm_of l::'v) = - l"
                by (metis Pos_atm_of_iff uminus_Pos)
              hence ff5: "\<And>l. - l \<notin># D \<or> l \<in> lits_of (trail S)"
                using ff4 ff3 ff2 by (metis (no_types) Neg_atm_of_iff Pos_atm_of_iff
                  atms_of_s_def in_atms_of_s_decomp mem_set_mset_iff)
              have "(\<exists>l. mm \<notin> {{#- l#} |l. l \<in># D} \<or> l \<in># mm \<and> lits_of (trail S) \<Turnstile>l l)
              \<or> (\<forall>l. mm \<noteq> {#- l#} \<or> l \<notin># D)"
                using ff5 ff1 uminus_of_uminus_id true_lit_def by (metis (lifting)  zero_less_Suc)
              hence "\<exists>l. mm \<notin> {{#- l#} |l. l \<in># D} \<or> l \<in># mm \<and> lits_of (trail S) \<Turnstile>l l"
                by blast }
              thus ?thesis unfolding CNot_def true_annots_def true_annot_def Ball_def lits_of_def
              true_cls_def atms_of_def Bex_mset_def
                by presburger
          qed
        hence False
          proof -
            obtain S' where
              f2: "full0 cdcl_cp S S'"
              by (meson alien always_exists_full_cdcl_cp_step local.finite)
            hence "S' = S"
              using cdcl_s.conflict'[of S] by (metis (no_types) full0_unfold termi)
            thus ?thesis
              using f2 \<open>D \<in> init_clss S\<close> \<open>conflicting S = C_True\<close> \<open>trail S \<Turnstile>as CNot D\<close>
              clauses_def full0_cdcl_cp_not_any_negated_init_clss by auto
          qed
    }
    hence "?M \<Turnstile>as ?N" by blast
  }
  moreover {
    assume "\<exists>D L. conflicting S = C_Clause (D + {#L#})"
    obtain D L where LD: "conflicting S = C_Clause (D + {#L#})"
      and "get_level L ?M = ?k"
      proof -
        obtain mm :: "'v literal multiset" and ll :: "'v literal" where
          f2: "conflicting S = C_Clause (mm + {#ll#})"
          using \<open>\<exists>D L. conflicting S = C_Clause (D + {#L#})\<close> by force
        have "\<forall>m. (conflicting S \<noteq> C_Clause m \<or> m = {#})
          \<or> (\<exists>l. l \<in># m \<and> get_level l (trail S) = backtrack_lvl S)"
          using confl_k by blast
        thus ?thesis
          using f2 that by (metis (no_types) multi_member_split single_not_empty union_eq_empty)
      qed
    let ?D = "D + {#L#}"
    have "?D \<noteq> {#}" by auto
    have "?M \<Turnstile>as CNot ?D" using confl LD unfolding cdcl_conflicting_def by auto
    hence "?M \<noteq> []" unfolding true_annots_def Ball_def true_annot_def true_cls_def by force
    { have M: "?M = hd ?M # tl ?M" using \<open>?M \<noteq> []\<close> list.collapse by fastforce
      assume marked: "is_marked (hd ?M)"
      then obtain k' where k': "k' + 1 = ?k"
        using level_inv M unfolding cdcl_M_level_inv_def
        by (cases "hd (trail S)"; cases "trail S") auto
      obtain L' l' where L': "hd ?M = Marked L' l'" using marked by (case_tac "hd ?M") auto
      have "get_all_levels_of_marked (hd (trail S) # tl (trail S))
        = rev [1..<1 + length (get_all_levels_of_marked ?M)]"
        using level_inv \<open>get_level L ?M = ?k\<close> M unfolding cdcl_M_level_inv_def M[symmetric] by blast
      hence l'_tl: "l' # get_all_levels_of_marked (tl ?M)
        = rev [1..<1 + length (get_all_levels_of_marked ?M)]" unfolding L' by simp
      moreover have "\<dots> = length (get_all_levels_of_marked ?M)
        # rev [1..<length (get_all_levels_of_marked ?M)]"
        using M Suc_le_mono calculation by (fastforce simp add: upt.simps(2))
      finally have
        "l' = ?k" and
        g_r: "get_all_levels_of_marked (tl (trail S))
          = rev [1..<length (get_all_levels_of_marked (trail S))]"
        using level_inv \<open>get_level L ?M = ?k\<close> M unfolding cdcl_M_level_inv_def by auto
      have *: "\<And>list. no_dup list \<Longrightarrow>
            - L \<in> lits_of list \<Longrightarrow> atm_of L \<in> atm_of ` lits_of list"
        by (metis atm_of_uminus imageI)
      have "L' = -L"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          moreover have "-L \<in> lits_of ?M" using confl LD unfolding cdcl_conflicting_def by auto
          ultimately have "get_level L (hd (trail S) # tl (trail S)) = get_level L (tl ?M)"
            using cdcl_M_level_inv_decomp(1)[OF level_inv] unfolding L' consistent_interp_def
            by (metis (no_types, lifting) L' M atm_of_eq_atm_of get_level_skip_beginning insert_iff
              lits_of_cons marked_lit.sel(1))

          moreover
            have "length (get_all_levels_of_marked (trail S)) = ?k"
              using level_inv unfolding cdcl_M_level_inv_def by auto
            hence "Max (set (0#get_all_levels_of_marked (tl (trail S)))) = ?k - 1"
              unfolding g_r by (auto simp add: Max_n_upt)
            hence "get_level L (tl ?M) < ?k"
              using get_maximum_possible_level_ge_get_level[of L "tl ?M"]
              by (metis One_nat_def add.right_neutral add_Suc_right diff_add_inverse2
                get_maximum_possible_level_max_get_all_levels_of_marked k' le_imp_less_Suc
                list.simps(15))
          finally show False using \<open>get_level L ?M = ?k\<close> M by auto
        qed
      have L: "hd ?M = Marked (-L) ?k"  using \<open>l' = ?k\<close> \<open>L' = -L\<close> L' by auto

      have g_a_l: "get_all_levels_of_marked ?M = rev [1..<1 + ?k]"
        using level_inv \<open>get_level L ?M = ?k\<close> M unfolding cdcl_M_level_inv_def by auto
      have g_k: "get_maximum_level D (trail S) \<le> ?k"
        using get_maximum_possible_level_ge_get_maximum_level[of D ?M]
          get_maximum_possible_level_max_get_all_levels_of_marked[of ?M]
        by (auto simp add: Max_n_upt g_a_l)
      have "get_maximum_level D (trail S) < ?k"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          hence "get_maximum_level D (trail S) = ?k" using M g_k unfolding L by auto
          then obtain L' where "L' \<in># D" and L_k: "get_level L' ?M = ?k"
            using get_maximum_level_exists_lit[of ?k D ?M] unfolding k'[symmetric] by auto
          have "L \<noteq> L'" using no_dup  \<open>L' \<in># D\<close>
            unfolding distinct_cdcl_state_def LD by (metis add.commute add_eq_self_zero
              count_single count_union less_not_refl3 distinct_mset_def union_single_eq_member)
          have "L' = -L"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              hence "get_level L' ?M = get_level L' (tl ?M)"
                using M \<open>L \<noteq> L'\<close> get_level_skip_beginning[of L' "hd ?M" "tl ?M"] unfolding L
                by (auto simp add: atm_of_eq_atm_of)
              moreover have "\<dots> < ?k"
                using level_inv g_r get_rev_level_less_max_get_all_levels_of_marked[of L' 0
                  "rev (tl ?M)"] L_k l'_tl calculation g_a_l
                by (auto simp add: Max_n_upt cdcl_M_level_inv_def)
              finally show False using L_k by simp
            qed
          hence taut: "tautology (D + {#L#})"
            using \<open>L' \<in># D\<close> by (metis add.commute mset_leD mset_le_add_left multi_member_this
              tautology_minus)
          have "consistent_interp (lits_of ?M)" using level_inv by auto
          hence "\<not>?M \<Turnstile>as CNot ?D"
            using taut by (metis (no_types) \<open>L' = - L\<close> \<open>L' \<in># D\<close> add.commute consistent_interp_def
              in_CNot_implies_uminus(2) mset_leD mset_le_add_left multi_member_this)
          moreover have "?M \<Turnstile>as CNot ?D"
            using confl no_dup LD unfolding cdcl_conflicting_def by auto
          ultimately show False by blast
        qed
      hence False
        using backtrack_no_decomp[OF _ \<open>get_level L (trail S) = backtrack_lvl S\<close> _ level_inv]
        LD  alien local.finite termi by (metis cdcl_then_exists_cdcl_s_step)
    }
    moreover {
      assume "\<not>is_marked (hd ?M)"
      then obtain L' C where L'C: "hd ?M = Propagated L' C" by (case_tac "hd ?M", auto)
      hence M: "?M = Propagated L' C # tl ?M" using \<open>?M \<noteq> []\<close>  list.collapse by fastforce
      then obtain C' where C': "cls_of_mark C = C' + {#L'#}"
        using confl unfolding cdcl_conflicting_def by (metis append_Nil diff_single_eq_union)
      { assume "-L' \<notin># ?D"
        hence False
          using bj[OF cdcl_bj.skip[OF skipping[OF _ \<open>-L' \<notin># ?D\<close> \<open>?D \<noteq> {#}\<close>, of S C "tl (trail S)" _
            ]]]
          termi M by (metis LD alien cdcl_then_exists_cdcl_s_step finite)
      }
      moreover {
        assume "-L' \<in># ?D"
        then obtain D' where D': "?D = D' + {#-L'#}" by (metis insert_DiffM2)
        have g_r: "get_all_levels_of_marked (Propagated L' C # tl (trail S))
          = rev [Suc 0..<Suc (length (get_all_levels_of_marked (trail S)))]"
          using level_inv M unfolding cdcl_M_level_inv_def by auto
        have "Max (insert 0 (set (get_all_levels_of_marked (Propagated L' C # tl (trail S))))) = ?k"
          using level_inv M unfolding g_r by (auto simp add:Max_n_upt)
        hence "get_maximum_level D' (Propagated L' C # tl ?M) \<le> ?k"
          using get_maximum_possible_level_ge_get_maximum_level[of D' "Propagated L' C # tl ?M"]
          unfolding get_maximum_possible_level_max_get_all_levels_of_marked by auto
        hence "get_maximum_level D' (Propagated L' C # tl ?M) = ?k
          \<or> get_maximum_level D' (Propagated L' C # tl ?M) < ?k"
          using le_neq_implies_less by blast
        moreover {
          assume g_D'_k: "get_maximum_level D' (Propagated L' C # tl ?M) = ?k"
          have False
            proof -
              have f1: "get_maximum_level D' (trail S) = backtrack_lvl S"
                using M g_D'_k by auto
              have "(trail S, init_clss S, learned_clss S, backtrack_lvl S, C_Clause (D + {#L#}))
                = state S"
                by (metis (no_types) LD)
              hence "cdcl_o S (update_conflicting (C_Clause (remdups_mset (D' + C'))) (tl_trail S))"
                using f1 bj[OF cdcl_bj.resolve[OF resolving[of S L' C' "tl ?M" ?N ?U ?k D']]]
                C' D' M by (metis mark_of_cls_cls_or_mark)
              thus ?thesis
                by (meson alien cdcl_then_exists_cdcl_s_step local.finite termi)
            qed
        }
        moreover {
          assume "get_maximum_level D' (Propagated L' C # tl ?M) < ?k"
          hence False
            proof -
              assume a1: "get_maximum_level D' (Propagated L' C # tl (trail S)) < backtrack_lvl S"
              obtain mm :: "'v literal multiset" and ll :: "'v literal" where
                f2: "conflicting S = C_Clause (mm + {#ll#})"
                    "get_level ll (trail S) = backtrack_lvl S"
                using LD \<open>get_level L (trail S) = backtrack_lvl S\<close> by blast
              hence f3: "get_maximum_level D' (trail S) \<le> get_level ll (trail S)"
                using M a1 by force
              have "get_level ll (trail S) \<noteq> get_maximum_level D' (trail S)"
                using f2 M calculation(2) by presburger
              have f1: "trail S = Propagated L' C # tl (trail S)"
                  "conflicting S = C_Clause (D' + {#- L'#})"
                using D' LD M by force+
              have f2: "conflicting S = C_Clause (mm + {#ll#}) "
                 "get_level ll (trail S) = backtrack_lvl S"
                using f2 by force+
              have "ll = - L'"
                by (metis (no_types) D' LD \<open>get_level ll (trail S) \<noteq> get_maximum_level D' (trail S)\<close>
                  conflicting_clause.inject f2 f3 get_maximum_level_ge_get_level insert_noteq_member
                  le_antisym)
              thus ?thesis
                using f2 f1 M backtrack_no_decomp[of S]
                by (metis (no_types) a1 alien cdcl_then_exists_cdcl_s_step level_inv finite termi)
            qed
        }
        ultimately have False by blast
      }
      ultimately have False by blast
    }
    ultimately have False by blast
  }
  ultimately show ?thesis by blast
qed

lemma cdcl_cp_tranclp_cdcl:
   "cdcl_cp S S' \<Longrightarrow> cdcl\<^sup>+\<^sup>+ S S'"
   apply (induct rule: cdcl_cp.induct)
   by (meson cdcl.conflict cdcl.propagate tranclp.r_into_trancl tranclp.trancl_into_trancl)+

lemma tranclp_cdcl_cp_tranclp_cdcl:
   "cdcl_cp\<^sup>+\<^sup>+ S S' \<Longrightarrow> cdcl\<^sup>+\<^sup>+ S S'"
   apply (induct rule: tranclp.induct)
    apply (simp add: cdcl_cp_tranclp_cdcl)
    by (meson cdcl_cp_tranclp_cdcl tranclp_trans)

lemma cdcl_s_tranclp_cdcl:
   "cdcl_s S S' \<Longrightarrow> cdcl\<^sup>+\<^sup>+ S S'"
proof (induct rule: cdcl_s.induct)
  case conflict'
  thus ?case
   unfolding full_def by (simp add: tranclp_cdcl_cp_tranclp_cdcl)
next
  case (other' S  S' S'')
  hence "S' = S'' \<or> cdcl_cp\<^sup>+\<^sup>+ S' S''"
    by (simp add: rtranclp_unfold full0_def)
  then show ?case
    using other' by (meson cdcl_cw_ops.other cdcl_cw_ops_axioms tranclp.r_into_trancl
      tranclp_cdcl_cp_tranclp_cdcl tranclp_trans)
qed

lemma tranclp_cdcl_s_tranclp_cdcl:
   "cdcl_s\<^sup>+\<^sup>+ S S' \<Longrightarrow> cdcl\<^sup>+\<^sup>+ S S'"
   apply (induct rule: tranclp.induct)
   using cdcl_s_tranclp_cdcl apply blast
   by (meson cdcl_s_tranclp_cdcl tranclp_trans)

lemma rtranclp_cdcl_s_rtranclp_cdcl:
   "cdcl_s\<^sup>*\<^sup>* S S' \<Longrightarrow> cdcl\<^sup>*\<^sup>* S S'"
  using rtranclp_unfold[of cdcl_s S S'] tranclp_cdcl_s_tranclp_cdcl[of S S'] by auto

lemma cdcl_o_conflict_is_false_with_level_inv:
  assumes "cdcl_o S S'"
  and "conflict_is_false_with_level S"
  and "distinct_cdcl_state S"
  and "cdcl_conflicting S"
  and "cdcl_M_level_inv S"
  shows "conflict_is_false_with_level S'"
  using assms
proof (induct rule: cdcl_o_induct)
  case (resolve L C M D) note tr_S = this(1) and confl = this(2) and IH = this(4) and n_d = this(5)
    and confl_inv = this(6) and M_lev = this(7)
  have "-L \<notin># D" using n_d confl unfolding distinct_cdcl_state_def distinct_mset_def by auto
  moreover have "L \<notin># D"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      moreover have "Propagated L (mark_of_cls (C + {#L#})) # M \<Turnstile>as CNot D"
        using confl_inv confl tr_S unfolding cdcl_conflicting_def by auto
      ultimately have "-L \<in> lits_of (Propagated L (mark_of_cls (C + {#L#})) # M)"
        using in_CNot_implies_uminus(2) by blast
      moreover have "no_dup (Propagated L (mark_of_cls (C + {#L#})) # M)"
        using M_lev tr_S unfolding cdcl_M_level_inv_def by auto
      ultimately show False unfolding lits_of_def by (metis consistent_interp_def image_eqI
        list.set_intros(1) lits_of_def marked_lit.sel(2) distinctconsistent_interp)
    qed

  ultimately
    have g_D: "get_maximum_level D (Propagated L (mark_of_cls (C + {#L#})) # M)
      = get_maximum_level D M"
    proof -
      have "\<forall>a f L. ((a::'v) \<in> f ` L) = (\<exists>l. (l::'v literal) \<in> L \<and> a = f l)"
        by blast
      thus ?thesis
        using get_maximum_level_skip_first[of L D "mark_of_cls (C + {#L#})" M] unfolding atms_of_def
        by (metis (no_types) \<open>- L \<notin># D\<close> \<open>L \<notin># D\<close> atm_of_eq_atm_of mem_set_mset_iff)
    qed
  { assume
      "get_maximum_level D (Propagated L (mark_of_cls (C + {#L#})) # M) = backtrack_lvl S" and
      "backtrack_lvl S > 0"
    hence D: "get_maximum_level D M = backtrack_lvl S" unfolding g_D by blast
    hence ?case
      using tr_S \<open>backtrack_lvl S > 0\<close> get_maximum_level_exists_lit[of "backtrack_lvl S" D M]
      by auto
  }
  moreover {
    assume [simp]: "backtrack_lvl S = 0"
    have "\<And>L. get_level L M = 0"
      proof -
        fix L
        have "atm_of L \<notin> atm_of ` (lits_of M) \<Longrightarrow> get_level L M = 0" by auto
        moreover {
          assume "atm_of L \<in> atm_of ` (lits_of M)"
          have g_r: "get_all_levels_of_marked M = rev [Suc 0..<Suc (backtrack_lvl S)]"
            using M_lev tr_S unfolding cdcl_M_level_inv_def by auto
          have "Max (insert 0 (set (get_all_levels_of_marked M))) = (backtrack_lvl S)"
            unfolding g_r by (simp add: Max_n_upt)
          hence "get_level L M = 0"
            using get_maximum_possible_level_ge_get_level[of L M]
            unfolding get_maximum_possible_level_max_get_all_levels_of_marked by auto
        }
        ultimately show "get_level L M = 0" by blast
      qed
    hence ?case using get_maximum_level_exists_lit_of_max_level[of "remdups_mset (D+C)" M] tr_S
      by (auto simp: Bex_mset_def)
  }
  ultimately show ?case using resolve.hyps(3) by blast
next
  case (skip L C' M D) note tr_S = this(1) and D = this(2) and confl_inv = this(7) and lev = this(8)
  then obtain La where "La \<in># D" and "get_level La (Propagated L C' # M) = backtrack_lvl S"
    using skip by auto
  moreover
    have "atm_of La \<noteq> atm_of L"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence La: "La = L" using \<open>La \<in># D\<close> \<open>- L \<notin># D\<close> by (auto simp add: atm_of_eq_atm_of)
        have "Propagated L C' # M \<Turnstile>as CNot D"
          using confl_inv tr_S D unfolding cdcl_conflicting_def by auto
        hence "-L \<in> lits_of M"
          using \<open>La \<in># D\<close> in_CNot_implies_uminus(2)[of D L "Propagated L C' # M"] unfolding La
          by auto
        thus False using lev tr_S unfolding cdcl_M_level_inv_def consistent_interp_def by auto
      qed
    hence "get_level La (Propagated L C' # M) = get_level La M"  by auto
  ultimately show ?case using D tr_S by auto
qed auto

subsubsection \<open>Strong completeness\<close>
lemma cdcl_cp_propagate_confl:
  assumes "cdcl_cp S T"
  shows "propagate\<^sup>*\<^sup>* S T \<or> (\<exists>S'. propagate\<^sup>*\<^sup>* S S' \<and> conflict S' T)"
  using assms by (induction) blast+

lemma rtranclp_cdcl_cp_propagate_confl:
  assumes "cdcl_cp\<^sup>*\<^sup>* S T"
  shows "propagate\<^sup>*\<^sup>* S T \<or> (\<exists>S'. propagate\<^sup>*\<^sup>* S S' \<and> conflict S' T)"
  by (simp add: assms rtranclp_cdcl_cp_propa_or_propa_confl)

lemma cdcl_cp_propagate_completeness:
  assumes MN: "set M \<Turnstile>s N" and
  cons: "consistent_interp (set M)" and
  tot: "total_over_m (set M) N" and
  "lits_of (trail S) \<subseteq> set M" and
  "init_clss S = N" and
  "propagate\<^sup>*\<^sup>* S S'" and
  "learned_clss S = {}"
  shows "length (trail S) \<le> length (trail S') \<and> lits_of (trail S') \<subseteq> set M"
  using assms(6,4,5,7)
proof (induction rule: rtranclp.induct)
  case rtrancl_refl
  thus ?case by auto
next
  case (rtrancl_into_rtrancl X Y Z)
  note st = this(1) and propa = this(2) and IH = this(3) and lits' = this(4) and NS = this(5) and
    learned = this(6)
  hence len: "length (trail X) \<le> length (trail Y)" and LM: "lits_of (trail Y) \<subseteq> set M"
     by blast+

  obtain M' N' U k C L where
    Y: "state Y = (M', N', U, k, C_True)" and
    Z: "state Z = (Propagated L (mark_of_cls (C + {#L#})) # M', N', U, k, C_True)" and
    C: "C + {#L#} \<in> clauses Y" and
    M'_C: "M' \<Turnstile>as CNot C" and
    "undefined_lit L (trail Y)"
    using propa by auto
  have "init_clss X = init_clss Y"
    using st by (simp add: rtranclp_cdcl_init_clss rtranclp_propagate_is_rtranclp_cdcl)
  then have [simp]: "N' = N" using NS Y Z by simp
  have "learned_clss Y = {}"
    using st learned by induction auto
  hence [simp]: "U = {}" using Y by auto
  have "set M \<Turnstile>s CNot C"
    using M'_C LM Y unfolding true_annots_def Ball_def true_annot_def true_clss_def true_cls_def
    by force
  moreover
    have "set M \<Turnstile> C + {#L#}"
      using MN C learned Y unfolding true_clss_def clauses_def by auto
  ultimately have "L \<in> set M" by (simp add: cons consistent_CNot_not)
  then show ?case using LM len Y Z by auto
qed

lemma completeness_is_a_full_propagation:
  fixes S :: "'st" and M :: "'v literal list"
  assumes MN: "set M \<Turnstile>s N"
  and cons: "consistent_interp (set M)"
  and tot: "total_over_m (set M) N"
  and fin: "finite (init_clss S)"
  and alien: "no_strange_atm S"
  and learned: "learned_clss S = {}"
  and clsS[simp]: "init_clss S = N"
  and lits: "lits_of (trail S) \<subseteq> set M"
  shows "\<exists>S'. propagate\<^sup>*\<^sup>* S S' \<and> full0 cdcl_cp S S'"
proof -
  obtain S' where full: "full0 cdcl_cp S S'"
    using always_exists_full_cdcl_cp_step alien fin by blast
  then consider (propa) "propagate\<^sup>*\<^sup>* S S'"
    | (confl) "\<exists>X. propagate\<^sup>*\<^sup>* S X \<and> conflict X S'"
    using rtranclp_cdcl_cp_propagate_confl unfolding full0_def by blast
  thus ?thesis
    proof cases
      case propa thus ?thesis using full by blast
    next
      case confl
      then obtain X where
        X: "propagate\<^sup>*\<^sup>* S X" and
        Xconf: "conflict X S'"
      by blast
      have clsX: "init_clss X = init_clss S"
        using rtranclp_cdcl_init_clss X rtranclp_propagate_is_rtranclp_cdcl by fast
      have learnedX: "learned_clss X = {}" using X learned by induction auto
      obtain E where
        E: "E \<in> init_clss X \<union> learned_clss X" and
        Not_E: "trail X \<Turnstile>as CNot E"
        using Xconf by (auto simp add: conflict.simps clauses_def)
      have "lits_of (trail X) \<subseteq> set M"
        using cdcl_cp_propagate_completeness[OF assms(1-3) lits _ X learned] learned by auto
      hence MNE: "set M \<Turnstile>s CNot E"
        using Not_E
        by (fastforce simp add: true_annots_def true_annot_def true_clss_def true_cls_def)
      have "\<not> set M \<Turnstile>s N"
         using E consistent_CNot_not[OF cons MNE]
         unfolding learnedX true_clss_def unfolding clsX clsS by blast
      thus ?thesis using MN by blast
    qed
qed

lemma rtranclp_propagate_is_update_trail: "propagate\<^sup>*\<^sup>* S T \<Longrightarrow> T = update_trail (trail T) S"
  by (induction rule: rtranclp_induct) (auto simp: cdcl_cp.simps st_equal)

lemma cdcl_cp_strong_completeness_n:
  assumes MN: "set M \<Turnstile>s N"
  and cons: "consistent_interp (set M)"
  and tot: "total_over_m (set M) N"
  and atm_incl: "atm_of ` (set M) \<subseteq> atms_of_m N"
  and "total_over_m (set M) N"
  and distM: "distinct M"
  and fin[simp]: "finite N"
  and length: "n \<le> length M"
  shows
    "\<exists>M' k. length M' \<ge>  n \<and>
      lits_of M' \<subseteq> set M \<and>
      rtranclp cdcl_s (init_state N) (update_backtrack_lvl k (update_trail M' (init_state N)))"
  using length
proof (induction n)
  case 0
  have "update_backtrack_lvl 0 (update_trail [] (init_state N)) = init_state N"
    by (auto simp: st_equal)
  hence
    "0 \<le> length []" and
    "lits_of [] \<subseteq> set M" and
    "cdcl_s\<^sup>*\<^sup>* (init_state N) (update_backtrack_lvl 0 (update_trail [] (init_state N)))"
    by auto
  thus ?case by blast
next
  case (Suc n) note IH = this(1) and n = this(2)
  then obtain M' k where
    l_M': "length M' \<ge> n" and
    M': "lits_of M' \<subseteq> set M" and
    st: "cdcl_s\<^sup>*\<^sup>* (init_state N) (update_backtrack_lvl k (update_trail M' (init_state N)))"
    by auto
    let ?S = "update_backtrack_lvl k (update_trail M' (init_state N))"
  have
    M: "cdcl_M_level_inv ?S" and
    alien: "no_strange_atm ?S"
      using rtranclp_cdcl_consistent_inv[OF rtranclp_cdcl_s_rtranclp_cdcl[OF st]]
      rtranclp_cdcl_no_strange_atm_inv[OF rtranclp_cdcl_s_rtranclp_cdcl[OF st]] by auto

  { assume no_step: "\<not>no_step propagate ?S"

    obtain S' where S': "propagate\<^sup>*\<^sup>* ?S S'" and full0: "full0 cdcl_cp ?S S'"
      using completeness_is_a_full_propagation[OF assms(1-3), of ?S] fin alien M' by auto
    hence "length (trail ?S) \<le> length (trail S') \<and> lits_of (trail S') \<subseteq> set M"
      using cdcl_cp_propagate_completeness[OF assms(1-3), of ?S] M' by auto
    moreover
      have full: "full cdcl_cp ?S S'"
        using full0 no_step no_step_cdcl_cp_no_conflict_no_propagate(2) unfolding full_def full0_def
        rtranclp_unfold by blast
      hence "cdcl_s ?S S'" by (simp add: cdcl_s.conflict')
    moreover {
      have "propagate\<^sup>+\<^sup>+ ?S S'" using S' full unfolding full_def by (metis rtranclpD tranclpD)
      moreover have "trail ?S = M'" by auto
      ultimately have "length (trail S') > n"
        using l_M' by (induction rule: tranclp.induct) auto}
    moreover
      have stS': "cdcl_s\<^sup>*\<^sup>* (init_state N) S'"
        using st cdcl_s.conflict'[OF full] by auto
      then have "init_clss S' = N" using stS' rtranclp_cdcl_s_no_more_init_clss by fastforce
    moreover
      have S'_S: "S' = update_trail (trail S') ?S"
        by (simp add: S' rtranclp_propagate_is_update_trail)
      hence S_S': "S' = update_backtrack_lvl (backtrack_lvl S')
        (update_trail (trail S') (init_state N))"
        by (auto simp: st_equal)
      have "cdcl_s\<^sup>*\<^sup>* (init_state (init_clss S'))
             (update_backtrack_lvl (backtrack_lvl S')
               (update_trail (trail S') (init_state (init_clss S'))))"
        apply (rule rtranclp.rtrancl_into_rtrancl)
        using st unfolding \<open>init_clss S' = N\<close> apply simp
        using \<open>cdcl_s ?S S'\<close>  unfolding \<open>init_clss S' = N\<close> S_S'[symmetric] by simp
    ultimately have ?case
      apply -
      apply (rule exI[of _ "trail S'"], rule exI[of _ "backtrack_lvl S'"])
      by auto
  }
  moreover {
    assume no_step: "no_step propagate ?S"
    have ?case
      proof (cases "length M' \<ge> Suc n")
        case True
        thus ?thesis using l_M' M' st M alien by blast
      next
        case False
        hence n': "length M' = n" using l_M' by auto
        have no_confl: "no_step conflict ?S"
          proof -
            { fix D
              assume "D \<in> N" and "M' \<Turnstile>as CNot D"
              hence "set M \<Turnstile> D" using MN unfolding true_clss_def by auto
              moreover have "set M \<Turnstile>s CNot D"
                using \<open>M' \<Turnstile>as CNot D\<close> M'
                by (meson true_annots_true_cls true_cls_mono_set_mset_l true_clss_def)
              ultimately have False using cons consistent_CNot_not by blast
            }
            thus ?thesis by (auto simp add: conflict.simps true_clss_def)
          qed
        have lenM: "length M = card (set M)" using distM by (induction M) auto
        have "no_dup M'" using M unfolding cdcl_M_level_inv_def by simp
        hence "card (lits_of M') = length M'"
          by (induction M') (auto simp add: lits_of_def card_insert_if)
        hence "lits_of M' \<subset> set M"
          using n M' n' lenM by auto
        then obtain m where m: "m \<in> set M" and undef_m: "m \<notin> lits_of M'" by auto
        moreover have "undefined_lit m M'"
          using M' Marked_Propagated_in_iff_in_lits_of calculation(1,2) cons
          consistent_interp_def by blast
        ultimately
          have dec: "decided ?S (cons_trail (Marked m (k+1)) (incr_lvl ?S))"
          using atm_incl decided.intros[of ?S M' N _ k m]  by auto
        let ?S' = "cons_trail (Marked m (k+1)) (incr_lvl ?S)"
        have "lits_of (trail ?S') \<subseteq> set M" using m M' by auto
        moreover have "finite (init_clss ?S')"
          using fin by auto
        moreover have "no_strange_atm ?S'"
          using alien dec by (meson cdcl_no_strange_atm_inv decided other)
        ultimately obtain S'' where S'': "propagate\<^sup>*\<^sup>* ?S' S''" and full0: "full0 cdcl_cp ?S' S''"
          using completeness_is_a_full_propagation[OF assms(1-3), of ?S'] by auto
        hence "length (trail ?S') \<le> length (trail S'') \<and> lits_of (trail S'') \<subseteq> set M"
          using cdcl_cp_propagate_completeness[OF assms(1-3), of ?S' S''] m M' by simp
        hence "Suc n \<le> length (trail S'') \<and> lits_of (trail S'') \<subseteq> set M"
          using l_M' by auto
        moreover
          have S'': "S'' =
            update_backtrack_lvl (backtrack_lvl S'') (update_trail (trail S'') (init_state N))"
            using rtranclp_propagate_is_update_trail[OF S''] by (auto simp: st_equal)
          hence "cdcl_s\<^sup>*\<^sup>* (init_state N)
              (update_backtrack_lvl (backtrack_lvl S'') (update_trail (trail S'') (init_state N)))"
            using cdcl_s.intros(2)[OF decided[OF dec] _ full0] no_step no_confl st
            by (metis (no_types, lifting) cdcl_cp.cases rtranclp.rtrancl_into_rtrancl)
        ultimately show ?thesis by blast
      qed
  }
  ultimately show ?case by blast
qed

lemma cdcl_cp_strong_completeness:
  assumes MN: "set M \<Turnstile>s N"
  and cons: "consistent_interp (set M)"
  and tot: "total_over_m (set M) N"
  and atm_incl: "atm_of ` (set M) \<subseteq> atms_of_m N"
  and "total_over_m (set M) N"
  and distM: "distinct M"
  and fin[simp]: "finite N"
  shows
    "\<exists>M' k.
      lits_of M' = set M \<and>
      rtranclp cdcl_s (init_state N) (update_backtrack_lvl k (update_trail M' (init_state N))) \<and>
      final_cdcl_state (update_backtrack_lvl k (update_trail M' (init_state N)))"
proof -
  from cdcl_cp_strong_completeness_n[OF assms, of "length M"]
  obtain M' k where
    l: "length M \<le> length M'" and
    M'_M: "lits_of M' \<subseteq> set M" and
    st: "cdcl_s\<^sup>*\<^sup>* (init_state N) (update_backtrack_lvl k (update_trail M' (init_state N)))"
    by auto
  let ?T = "(update_backtrack_lvl k (update_trail M' (init_state N)))"
  have "card (set M) = length M" using distM by (simp add: distinct_card)
  moreover
    have "cdcl_M_level_inv ?T"
      using rtranclp_cdcl_s_consistent_inv[OF st] by auto
    hence no_dup: "no_dup M'" by auto
    hence "card (set ((map (\<lambda>l. atm_of (lit_of l)) M'))) = length M'"
      using distinct_card by fastforce
  moreover have "card (lits_of M') = card (set ((map (\<lambda>l. atm_of (lit_of l)) M')))"
    using no_dup unfolding lits_of_def apply (induction M') by (auto simp add: card_insert_if)
  ultimately have "card (set M) \<le> card (lits_of M')" using l unfolding lits_of_def by auto
  hence "set M = lits_of M'"
    using M'_M  card_seteq by blast
  moreover
    hence "M' \<Turnstile>as N"
      using MN unfolding true_annots_def Ball_def true_annot_def true_clss_def by auto
    hence "final_cdcl_state ?T"
      unfolding final_cdcl_state_def by auto
  ultimately show ?thesis using st by blast
qed

subsubsection \<open>No conflict with only variables of level less than backtrack level\<close>
text \<open>This invariant is stronger than the previous argument in the sense that it is a property about
  all possible conflicts.\<close>
abbreviation "no_littler_confl (S::'st) \<equiv>
  (\<forall>M K i M' D. M' @ Marked K i # M = trail S \<longrightarrow> D \<in> clauses S
    \<longrightarrow> \<not>M \<Turnstile>as CNot D)"

lemma "finite N \<Longrightarrow> no_littler_confl (init_state N)" by auto

lemma cdcl_o_no_littler_confl_inv:
  fixes S S' :: "'st"
  assumes "cdcl_o S S'"
  and "conflict_is_false_with_level S"
  and "no_littler_confl S"
  and "cdcl_M_level_inv S"
  and "no_clause_is_false S"
  shows "no_littler_confl S'"
  using assms
proof (induct rule: cdcl_o_induct)
  case (decided L) note confl = this(1) and no_f = this(7) and IH = this(5) and lev = this(6)
  show ?case
    proof (intro allI impI)
      fix M'' K i M' Da
      assume "M'' @ Marked K i # M' = trail (cons_trail (Marked L (backtrack_lvl S + 1)) (incr_lvl S))"
      and D: "Da \<in> local.clauses (cons_trail (Marked L (backtrack_lvl S + 1)) (incr_lvl S))"
      then have "tl M'' @ Marked K i # M' = trail S
        \<or> (M'' = [] \<and> Marked K i # M' = Marked L (backtrack_lvl S + 1) # trail S)"
        by (cases M'') auto
      moreover {
        assume "tl M'' @ Marked K i # M' = trail S"
        hence "\<not>M' \<Turnstile>as CNot Da" using IH D by auto
      }
      moreover {
        assume "Marked K i # M' = Marked L (backtrack_lvl S + 1) # trail S"
        hence "\<not>M' \<Turnstile>as CNot Da" using no_f D confl by auto
      }
      ultimately show "\<not>M' \<Turnstile>as CNot Da" by fast
   qed
next
  case resolve
  thus ?case by force
next
  case skip
  thus ?case by force
next
  case (backtrack K i M1 M2 L D) note decomp = this(1) and confl = this(3) and IH = this(7) and
    lev = this(8)
  obtain c where M: "trail S = c @ M2 @ Marked K (i+1) # M1"
    using decomp by auto

  show ?case
    proof (intro allI impI)
      fix M ia K' M' Da
      assume "M' @ Marked K' ia # M =
        trail (update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1)
          (add_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True S))))"
      hence "tl M' @ Marked K' ia # M = M1"
        by (cases M') auto
      assume D: "Da \<in> clauses (update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1)
        (add_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True S))))"
      moreover{
        assume "Da \<in> clauses S"
        hence "\<not>M \<Turnstile>as CNot Da" using IH \<open>tl M' @ Marked K' ia # M = M1\<close> M confl by auto
      }
      moreover {
        assume Da: "Da = D + {#L#}"
        have "\<not>M \<Turnstile>as CNot Da"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            hence "-L \<in> lits_of M" unfolding Da by auto
            hence "-L \<in> lits_of (Propagated L (mark_of_cls(D + {#L#})) # M1)"
              using UnI2 \<open>tl M' @ Marked K' ia # M = M1\<close>
              by auto
            moreover
              have "backtrack S
                (update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1) (add_cls (D + {#L#})
                  (update_backtrack_lvl i (update_conflicting C_True S))))"
                 using backtrack.intros[of S] backtrack.hyps by force
              hence "cdcl_M_level_inv
                (update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1) (add_cls (D + {#L#})
                  (update_backtrack_lvl i (update_conflicting C_True S))))"
                using cdcl_consistent_inv[OF _ lev] other[OF bj] by auto
              hence "no_dup  (Propagated L (mark_of_cls (D + {#L#})) # M1)" by auto
            ultimately show False apply simp by (metis atm_of_uminus imageI image_image lits_of_def)
          qed
      }
      ultimately show "\<not>M \<Turnstile>as CNot Da" by auto
    qed
qed

lemma conflict_no_littler_confl_inv:
  assumes "conflict S S'"
  and "no_littler_confl S"
  shows "no_littler_confl S'"
  using assms by fastforce

lemma propagate_no_littler_confl_inv:
  assumes propagate: "propagate S S'"
  and n_l: "no_littler_confl S"
  shows "no_littler_confl S'"
proof (intro allI impI)
  fix M' K i M'' D
  assume M': "M'' @ Marked K i # M' = trail S'"
  and "D \<in> clauses S'"
  obtain M N U k C L where
    S: "state S = (M, N, U, k, C_True)" and
    S': "state S' = (Propagated L (mark_of_cls (C + {#L#})) # M, N, U, k, C_True)" and
    "C + {#L#} \<in> clauses S" and
    "M \<Turnstile>as CNot C" and
    "undefined_lit L M"
    using propagate by auto
  have "tl M'' @ Marked K i # M' = trail S" using M' S S'
    by (metis Pair_inject list.inject list.sel(3) marked_lit.distinct(1) self_append_conv2
      tl_append2)
  hence "\<not>M' \<Turnstile>as CNot D " using \<open>D \<in> clauses S'\<close> n_l S S' clauses_def by auto
  thus "\<not>M' \<Turnstile>as CNot D" by auto
qed

lemma cdcl_cp_no_littler_confl_inv:
  assumes propagate: "cdcl_cp S S'"
  and n_l: "no_littler_confl S"
  shows "no_littler_confl S'"
  using assms
proof (induct rule: cdcl_cp.induct)
  case (conflict' S S')
  thus ?case using conflict_no_littler_confl_inv[of S S'] by blast
next
  case (propagate' S S')
  thus ?case using propagate_no_littler_confl_inv[of S S'] by fastforce
qed

lemma rtrancp_cdcl_cp_no_littler_confl_inv:
  assumes propagate: "cdcl_cp\<^sup>*\<^sup>* S S'"
  and n_l: "no_littler_confl S"
  shows "no_littler_confl S'"
  using assms
proof (induct rule: rtranclp.induct)
  case rtrancl_refl
  thus ?case by simp
next
  case (rtrancl_into_rtrancl S S' S'')
  thus ?case using cdcl_cp_no_littler_confl_inv[of S' S''] by fast
qed

lemma trancp_cdcl_cp_no_littler_confl_inv:
  assumes propagate: "cdcl_cp\<^sup>+\<^sup>+ S S'"
  and n_l: "no_littler_confl S"
  shows "no_littler_confl S'"
  using assms
proof (induct rule: tranclp.induct)
  case (r_into_trancl S S')
  thus ?case using cdcl_cp_no_littler_confl_inv[of S S'] by blast
next
  case (trancl_into_trancl S S' S'')
  thus ?case using cdcl_cp_no_littler_confl_inv[of S' S''] by fast
qed

lemma full0_cdcl_cp_no_littler_confl_inv:
  assumes "full0 cdcl_cp S S'"
  and n_l: "no_littler_confl S"
  shows "no_littler_confl S'"
  using assms unfolding full0_def
  using rtrancp_cdcl_cp_no_littler_confl_inv[of S S'] by blast

lemma full_cdcl_cp_no_littler_confl_inv:
  assumes "full cdcl_cp S S'"
  and n_l: "no_littler_confl S"
  shows "no_littler_confl S'"
  using assms unfolding full_def
  using trancp_cdcl_cp_no_littler_confl_inv[of S S'] by blast

lemma cdcl_s_no_littler_confl_inv:
  assumes "cdcl_s S S'"
  and n_l: "no_littler_confl S"
  and "conflict_is_false_with_level S"
  and "cdcl_M_level_inv S"
  shows "no_littler_confl S'"
  using assms
proof (induct rule: cdcl_s.induct)
  case (conflict' S S')
  thus ?case using full_cdcl_cp_no_littler_confl_inv[of S S'] by blast
next
  case (other' S S' S'')
  have "no_littler_confl S'"
    using cdcl_o_no_littler_confl_inv[OF other'.hyps(1) other'.prems(2,1,3)]
    not_conflict_not_any_negated_init_clss other'.hyps(2) by blast
  thus ?case using full0_cdcl_cp_no_littler_confl_inv[of S' S''] other'.hyps by blast
qed


lemma conflict_conflict_is_no_clause_is_false_test:
  assumes "conflict S S'"
  and "(\<forall>D \<in> init_clss S \<union> learned_clss S. trail S \<Turnstile>as CNot D
    \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S) = backtrack_lvl S))"
  shows "\<forall>D \<in> init_clss S' \<union> learned_clss S'. trail S' \<Turnstile>as CNot D
    \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S') = backtrack_lvl S')"
  using assms by auto

lemma is_conflicting_exists_conflict:
  assumes "\<not>(\<forall>D\<in>init_clss S' \<union> learned_clss S'. \<not> trail S' \<Turnstile>as CNot D)"
  and "conflicting S' = C_True"
  shows "\<exists>S''. conflict S' S''"
  using assms by (auto simp: conflict.simps clauses_def)

lemma cdcl_o_conflict_is_no_clause_is_false:
  fixes S S' :: "'st"
  assumes "cdcl_o S S'"
  and "conflict_is_false_with_level S"
  and "no_clause_is_false S"
  and "cdcl_M_level_inv S"
  and "no_littler_confl S"
  shows "no_clause_is_false S'
    \<or> (conflicting S' = C_True
        \<longrightarrow> (\<forall>D \<in> clauses S'. trail S' \<Turnstile>as CNot D
             \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S') = backtrack_lvl S')))"
  using assms
proof (induct rule: cdcl_o_induct)
  case (decided L) note S = this(1) and undef = this(2) and no_f = this(5) and lev = this(6)
  show ?case
    proof (rule HOL.disjI2, clarify)
      fix D
      assume D: "D \<in> clauses (cons_trail (Marked L (backtrack_lvl S + 1)) (incr_lvl S))"
      and M_D: "trail (cons_trail (Marked L (backtrack_lvl S + 1)) (incr_lvl S)) \<Turnstile>as CNot D"
    let ?M = "trail S"
    let ?M' = "trail (cons_trail (Marked L (backtrack_lvl S + 1)) (incr_lvl S))"
    let ?k = "backtrack_lvl S"
    have "\<not>?M \<Turnstile>as CNot D"
        using no_f D S by auto
      have "-L \<in># D"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          have "?M \<Turnstile>as CNot D"
            unfolding true_annots_def Ball_def true_annot_def CNot_def true_cls_def
            proof (intro allI impI)
              fix x
              assume x: "x \<in> {{#- L#} |L. L \<in># D}"
              then obtain L' where L': "x = {#-L'#}" "L' \<in># D" by auto
              obtain L'' where "L'' \<in># x" and "lits_of (Marked L (?k + 1) # ?M) \<Turnstile>l L''"
                using M_D x unfolding true_annots_def Ball_def true_annot_def CNot_def true_cls_def
                Bex_mset_def by auto
              show "\<exists>L \<in># x. lits_of ?M \<Turnstile>l L" unfolding Bex_mset_def
                by (metis \<open>- L \<notin># D\<close> \<open>L'' \<in># x\<close> L' \<open>lits_of (Marked L (?k + 1) # ?M) \<Turnstile>l L''\<close>
                  count_single insertE less_numeral_extra(3) lits_of_cons marked_lit.sel(1)
                  true_lit_def uminus_of_uminus_id)
            qed
          thus False using \<open>\<not> ?M \<Turnstile>as CNot D\<close> by auto
        qed
      have "atm_of L \<notin> atm_of ` (lits_of ?M)"
        using undef defined_lit_map unfolding lits_of_def by fastforce
      hence "get_level (-L) (Marked L (?k + 1) # ?M) = ?k + 1" by simp
      thus "\<exists>La. La \<in># D \<and> get_level La ?M'
        = backtrack_lvl (cons_trail (Marked L (backtrack_lvl S + 1)) (incr_lvl S))"
        using \<open>-L \<in># D\<close> by auto
    qed
next
  case (resolve)
  thus ?case by auto
next
  case (skip)
  thus ?case by auto
next
  case (backtrack K i M1 M2 L D) note decomp = this(1) and lev = this(8) and no_f = this(7)
    and no_l = this(9)
  show ?case
    proof (rule HOL.disjI2, clarify)
      fix Da
      assume Da: "Da \<in> local.clauses (update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1)
        (add_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True S))))"
      and M_D: "trail (update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1)
        (add_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True S)))) \<Turnstile>as CNot Da"
      let ?T = "update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1)
        (add_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True S)))"
      obtain c where M: "trail S = c @ M2 @ Marked K (i + 1) # M1"
        using decomp by auto
      have "backtrack S ?T"
       using backtrack.intros backtrack.hyps by force
      hence lev': "cdcl_M_level_inv ?T"
        using cdcl_consistent_inv lev other by blast
      hence "- L \<notin> lits_of M1"
        unfolding cdcl_M_level_inv_def lits_of_def
        proof -
          have "consistent_interp (lits_of (trail S)) \<and> no_dup (trail S)
            \<and> backtrack_lvl S = length (get_all_levels_of_marked (trail S))
            \<and> get_all_levels_of_marked (trail S)
              = rev [1..<1 + length (get_all_levels_of_marked (trail S))]"
            using assms(4) cdcl_cw_ops.cdcl_M_level_inv_def cdcl_cw_ops_axioms by blast
          then show "- L \<notin> lit_of ` set M1"
            by (metis (no_types) One_nat_def add.right_neutral add_Suc_right
              atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set backtrack.hyps(2)
              cdcl_cw_ops.backtrack_lit_skiped cdcl_cw_ops_axioms decomp lits_of_def) (* 135 ms *)
        qed
      { assume "Da \<in> clauses S"
        hence "~M1 \<Turnstile>as CNot Da" using no_l M by auto
      }
      moreover {
        assume Da: "Da = D + {#L#}"
        have "~M1 \<Turnstile>as CNot Da" using \<open>- L \<notin> lits_of M1\<close> unfolding Da by simp
      }
      ultimately have "~M1 \<Turnstile>as CNot Da" using Da by auto
      hence "-L \<in># Da"
        by (metis M_D \<open>- L \<notin> lits_of M1\<close> in_CNot_implies_uminus(2) insert_iff lits_of_cons
          marked_lit.sel(2) trail_update_trail true_annots_CNot_lit_of_notin_skip)
      have g_M1: "get_all_levels_of_marked M1 = rev [1..<i+1]"
        using lev' unfolding cdcl_M_level_inv_def by auto
      have "no_dup (Propagated L (mark_of_cls (D + {#L#})) # M1)" using lev' by auto
      hence L: "atm_of L \<notin> atm_of ` lits_of M1" unfolding lits_of_def by auto
      have "get_level (-L) (Propagated L (mark_of_cls(D + {#L#})) # M1) = i"
        using get_level_get_rev_level_get_all_levels_of_marked[OF L,
          of "[Propagated L (mark_of_cls(D + {#L#}))]"]
        by (simp add: g_M1 split: if_splits)
      thus "\<exists>La. La \<in># Da \<and>
        get_level La (trail (update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1)
          (add_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True S)))))
        =
        backtrack_lvl (update_trail (Propagated L (mark_of_cls (D + {#L#})) # M1)
          (add_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True S))))"
        using \<open>-L \<in># Da\<close> by auto
    qed
qed

(*TODO Move*)
lemma full_cdcl_cp_exists_conflict_decompose:
  assumes confl: "\<exists>D\<in>clauses S. trail S \<Turnstile>as CNot D"
  and full: "full0 cdcl_cp S U"
  and no_confl: "conflicting S = C_True"
  shows "\<exists>T. propagate\<^sup>*\<^sup>* S T \<and> conflict T U"
proof -
  consider (propa) "propagate\<^sup>*\<^sup>* S U"
        |  (confl) T where "propagate\<^sup>*\<^sup>* S T" and "conflict T U"
   using full unfolding full0_def by (blast dest:rtranclp_cdcl_cp_propa_or_propa_confl)
  thus ?thesis
    proof cases
      case confl
      thus ?thesis by blast
    next
      case propa
      hence "conflicting U = C_True"
        using no_confl by (induction) auto
      moreover have [simp]: "learned_clss U = learned_clss S" and [simp]: "init_clss U = init_clss S"
        using propa by induction auto
      moreover
        obtain D where D: "D\<in>clauses U" and
          trS: "trail S \<Turnstile>as CNot D"
          using confl clauses_def by auto
        obtain M where M: "trail U = M @ trail S"
          using full rtranclp_cdcl_cp_dropWhile_trail unfolding full0_def by blast
        have tr_U: "trail U \<Turnstile>as CNot D"
          apply (rule true_annots_mono)
          using trS unfolding M by simp_all
      have "\<exists>V. conflict U V"
        using \<open>conflicting U = C_True\<close> D clauses_def not_conflict_not_any_negated_init_clss tr_U
        by blast
      hence False using full cdcl_cp.conflict' unfolding full0_def by blast
      thus ?thesis by fast
    qed
qed

lemma full_cdcl_cp_exists_conflict_full_decompose:
  assumes confl: "\<exists>D\<in>clauses S. trail S \<Turnstile>as CNot D"
  and full: "full0 cdcl_cp S U"
  and no_confl: "conflicting S = C_True"
  shows "\<exists>T D. propagate\<^sup>*\<^sup>* S T \<and> conflict T U
    \<and> trail T \<Turnstile>as CNot D \<and> conflicting U = C_Clause D \<and> D \<in> clauses S"
proof -
  obtain T where propa: "propagate\<^sup>*\<^sup>* S T" and conf: "conflict T U"
    using full_cdcl_cp_exists_conflict_decompose[OF assms] by blast
  have p: "learned_clss T = learned_clss S" "init_clss T = init_clss S"
     using propa by induction auto
  have c: "learned_clss U = learned_clss T" "init_clss U = init_clss T"
     using conf by induction auto
  obtain D where "trail T \<Turnstile>as CNot D \<and> conflicting U = C_Clause D \<and> D \<in> clauses S"
    using conf p c by (auto elim!: conflictE simp: clauses_def)
  thus ?thesis
    using propa conf by blast
qed

lemma cdcl_s_no_littler_confl_inv_ex_lit_of_max_level:
  assumes "cdcl_s S S'"
  and n_l: "no_littler_confl S"
  and "conflict_is_false_with_level S"
  and "cdcl_M_level_inv S"
  and "no_clause_is_false S"
  and "distinct_cdcl_state S"
  and "cdcl_conflicting S"
  shows "no_littler_confl S' \<and> conflict_is_false_with_level S'"
  using assms
proof (induct rule: cdcl_s.induct)
  case (conflict' S S')
  have "no_littler_confl S'"
    using conflict'.hyps conflict'.prems(1) full_cdcl_cp_no_littler_confl_inv by blast
  moreover have "conflict_is_false_with_level S'"
    using conflict'.hyps conflict'.prems(2-4) rtranclp_cdcl_co_conflict_ex_lit_of_max_level[of S S']
    unfolding full0_def full_def rtranclp_unfold by blast
  ultimately show ?case by blast
next
  case (other' S S' S'')
  have lev': "cdcl_M_level_inv S'"
    using cdcl_consistent_inv other other'.hyps(1) other'.prems(3) by blast
  have "no_littler_confl S''"
    using cdcl_s_no_littler_confl_inv[OF cdcl_s.other'[OF other'.hyps(1-3)]] other'.prems(1-3)
    by blast
  moreover
  have "no_clause_is_false S'
    \<or> (conflicting S' = C_True \<longrightarrow> (\<forall>D\<in>clauses S'. trail S' \<Turnstile>as CNot D
        \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S') = backtrack_lvl S')))"
    using cdcl_o_conflict_is_no_clause_is_false[of S S'] other'.hyps(1) other'.prems(1-4) by fast
  moreover {
    assume "no_clause_is_false S'"
    {
      assume "conflicting S' = C_True"
      hence "conflict_is_false_with_level S'" by auto
      moreover have "full0 cdcl_cp S' S''"
        by (metis (no_types) other'.hyps(3))
      ultimately have "conflict_is_false_with_level S''"
        using rtranclp_cdcl_co_conflict_ex_lit_of_max_level[of S' S''] lev' \<open>no_clause_is_false S'\<close>
        by blast
    }
    moreover
    {
      assume c: "conflicting S' \<noteq> C_True"
      have "conflicting S \<noteq> C_True" using other'.hyps(1) c
        by (induct rule: cdcl_o_induct) auto
      hence "conflict_is_false_with_level S'"
        using cdcl_o_conflict_is_false_with_level_inv[OF other'.hyps(1) other'.prems(2)]
        other'.prems(3,5,6) by blast
      moreover have "cdcl_cp\<^sup>*\<^sup>* S' S''" using other'.hyps(3) unfolding full0_def by auto
      hence "S' = S''" using c
        by (induct rule: rtranclp.induct)
           (fastforce intro: conflicting_clause.exhaust)+
      ultimately have "conflict_is_false_with_level S''" by auto
    }
    ultimately have "conflict_is_false_with_level S''" by blast
  }
  moreover {
     assume confl: "conflicting S' = C_True"
     and D_L: "\<forall>D \<in> clauses S'. trail S' \<Turnstile>as CNot D
         \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S') = backtrack_lvl S')"
     { assume "\<forall>D\<in>clauses S'. \<not> trail S' \<Turnstile>as CNot D"
       hence "no_clause_is_false S'" using \<open>conflicting S' = C_True\<close> by simp
       hence "conflict_is_false_with_level S''" using calculation(3) by blast
     }
     moreover {
       assume "\<not>(\<forall>D\<in>clauses S'. \<not> trail S' \<Turnstile>as CNot D)"
       then obtain T D where
         "propagate\<^sup>*\<^sup>* S' T" and
         "conflict T S''" and
         D: "D \<in> clauses S'" and
         "trail S'' \<Turnstile>as CNot D" and
         "conflicting S'' = C_Clause D"
         using full_cdcl_cp_exists_conflict_full_decompose[OF _ _  \<open>conflicting S' = C_True\<close>]
         other'(3) by force
       obtain M where M: "trail S'' = M @ trail S'" and nm: "\<forall>m\<in>set M. \<not>is_marked m"
         using rtranclp_cdcl_cp_dropWhile_trail other'(3) unfolding full0_def by blast
       have btS: "backtrack_lvl S'' = backtrack_lvl S'"
         using other'.hyps(3) unfolding full0_def by (metis  rtranclp_cdcl_cp_backtrack_lvl)
       have inv: "cdcl_M_level_inv S''"
         by (metis (no_types) cdcl_s.conflict' cdcl_s_consistent_inv full0_unfold lev' other'.hyps(3))
       hence nd: "no_dup (trail S'')"
         by (metis (no_types) cdcl_M_level_inv_decomp(2))
       have "conflict_is_false_with_level S''"
         proof (cases)
           assume "trail S' \<Turnstile>as CNot D"
           moreover then obtain L where "L \<in># D" and "get_level L (trail S') = backtrack_lvl S'"
             using D_L D by blast
           moreover
             have LS': "-L \<in> lits_of (trail S')"
               using \<open>trail S' \<Turnstile>as CNot D\<close> \<open>L \<in># D\<close> in_CNot_implies_uminus(2) by blast
               (*TODO tune proof*)
             hence "atm_of L \<notin> atm_of ` lits_of M"
               using LS' nd unfolding M apply (auto simp add: lits_of_def)
               by (metis IntI atm_of_uminus empty_iff image_eqI)
             hence "get_level L (trail S'') = get_level L (trail S')"
               unfolding M by (simp add: lits_of_def)
           ultimately show ?thesis using btS \<open>conflicting S'' = C_Clause D\<close> by auto
         next
           assume "\<not>trail S' \<Turnstile>as CNot D"
           then obtain L where "L \<in># D" and LM: "-L \<in> lits_of M"
             using \<open>trail S'' \<Turnstile>as CNot D\<close>
               by (auto simp add: CNot_def true_cls_def  M true_annots_def true_annot_def
                     split: split_if_asm)
           (*TODO tune proof*)
           hence LS': "atm_of L \<notin> atm_of ` lits_of (trail S')"
             using nd unfolding M apply (auto simp add: lits_of_def)
             by (metis IntI atm_of_uminus empty_iff image_eqI)

           show ?thesis
             proof (cases)
               assume ne: "get_all_levels_of_marked (trail S') = []"
               have "backtrack_lvl S'' = 0"
                 using inv ne nm unfolding cdcl_M_level_inv_def M
                 by (simp add: get_all_levels_of_marked_nil_iff_not_is_marked)
               moreover
                 have a1: "get_rev_level L 0 (rev M) = 0"
                   using nm by auto
                 hence "get_level L (M @ trail S') = 0"
                   by (metis LS' get_all_levels_of_marked_nil_iff_not_is_marked
                     get_level_skip_beginning_not_marked lits_of_def ne)
               ultimately show ?thesis using \<open>conflicting S'' = C_Clause D\<close> \<open>L \<in># D\<close> unfolding M
                 by auto
           next
             assume ne: "get_all_levels_of_marked (trail S') \<noteq> []"
             have "hd (get_all_levels_of_marked (trail S')) = backtrack_lvl S'"
               using ne cdcl_M_level_inv_decomp(4)[OF lev'] M nm
               by (simp add: get_all_levels_of_marked_nil_iff_not_is_marked[symmetric])
             moreover have "atm_of L \<in> atm_of ` lits_of M "
                using \<open>-L \<in> lits_of M\<close>
                by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set lits_of_def)
             ultimately show ?thesis
               using nm ne \<open>L\<in>#D\<close> \<open>conflicting S'' = C_Clause D\<close>
                 get_level_skip_beginning_hd_get_all_levels_of_marked[OF LS', of M]
                 get_level_skip_in_all_not_marked[of "rev M" L "backtrack_lvl S'"]
               unfolding lits_of_def btS M
               by auto
          qed
         qed
     }
     ultimately have "conflict_is_false_with_level S''" by blast
  }
  moreover
  {
    assume "conflicting S' \<noteq> C_True"
    have "no_clause_is_false S'" using \<open>conflicting S' \<noteq> C_True\<close>  by auto
    hence "conflict_is_false_with_level S''" using calculation(3) by blast
  }
  ultimately show ?case by fast
qed

lemma rtranclp_cdcl_s_no_littler_confl_inv:
  assumes "cdcl_s\<^sup>*\<^sup>* S S'"
  and n_l: "no_littler_confl S"
  and "conflict_is_false_with_level S"
  and "cdcl_M_level_inv S"
  and "no_clause_is_false S"
  and "distinct_cdcl_state S"
  and "cdcl_conflicting S"
  and "all_decomposition_implies (init_clss S) (get_all_marked_decomposition (trail S))"
  and "cdcl_learned_clause S"
  and "no_strange_atm S"
  shows "no_littler_confl S' \<and> conflict_is_false_with_level S'"
  using assms
proof (induct rule: rtranclp.induct)
  case (rtrancl_refl S)
  thus ?case by auto
next
  case (rtrancl_into_rtrancl S S' S'') note st = this(1) and IH = this(2) and cls_false = this(7)
    and no_dup = this(8)
  have "no_littler_confl S'" and "conflict_is_false_with_level S'"
    using IH[OF rtrancl_into_rtrancl.prems] by blast+
  moreover have "cdcl_M_level_inv S'"
    using  st rtrancl_into_rtrancl.prems(3) rtranclp_cdcl_s_rtranclp_cdcl
    by (blast intro: rtranclp_cdcl_consistent_inv)+
  moreover have "no_clause_is_false S'"
    using st cls_false by (metis (mono_tags, lifting) cdcl_s_not_non_negated_init_clss rtranclp.simps)
  moreover have "distinct_cdcl_state S'"
    using rtanclp_distinct_cdcl_state_inv st no_dup rtranclp_cdcl_s_rtranclp_cdcl by blast
  moreover have "cdcl_conflicting S'"
    using rtranclp_cdcl_all_inv(6)[of S S'] st rtrancl_into_rtrancl.prems
    by (simp add: rtranclp_cdcl_s_rtranclp_cdcl)
  ultimately show ?case
    using cdcl_s_no_littler_confl_inv_ex_lit_of_max_level[OF rtrancl_into_rtrancl.hyps(3)] by fast
qed

subsubsection \<open>Final states are at the end\<close>
(*prop 2.10.7*)
lemma full_cdcl_s_normal_forms_non_false:
  fixes S' :: "'st"
  assumes full: "full0 cdcl_s (init_state N) S'"
  and no_d: "distinct_mset_set N"
  and finite[simp]: "finite N"
  and no_empty: "\<forall>D\<in>N. D \<noteq> {#}"
  shows "(conflicting S' = C_Clause {#} \<and> unsatisfiable (init_clss S'))
    \<or> (conflicting S' = C_True \<and> trail S' \<Turnstile>as init_clss S')"
proof -
  let ?S = "init_state N"
  have
    termi: "\<forall>S''. \<not>cdcl_s S' S''" and
    step: "cdcl_s\<^sup>*\<^sup>* (init_state N) S'" using full unfolding full0_def by auto
  moreover have "all_decomposition_implies (init_clss (init_state N))
                                          (get_all_marked_decomposition (fst (S0_cdcl N)))"
    by auto
  hence
    decomp: "all_decomposition_implies (init_clss S') (get_all_marked_decomposition (trail S'))" and
    learned: "cdcl_learned_clause S'" and
    level_inv: "cdcl_M_level_inv S'" and
    alien: "no_strange_atm S'" and
    no_dup: "distinct_cdcl_state S'" and
    confl: "cdcl_conflicting S'"
    using no_d tranclp_cdcl_s_tranclp_cdcl[of ?S S'] step rtranclp_cdcl_all_inv(1-6)[of ?S S']
    unfolding rtranclp_unfold by auto
  moreover
    have finite: "finite (init_clss S')"
      using rtranclp_cdcl_s_no_more_init_clss[OF step] finite by auto
  moreover
    have "\<forall>D\<in>N. \<not> [] \<Turnstile>as CNot D" using no_empty by auto
    hence confl_k: "conflict_is_false_with_level S'"
      using rtranclp_cdcl_s_no_littler_confl_inv[OF step] no_d by auto
  show ?thesis
    using cdcl_s_normal_forms[OF termi decomp learned level_inv alien no_dup confl finite confl_k] .
qed


lemma conflict_is_full_cdcl_cp:
  assumes cp: "conflict S S'"
  shows "full cdcl_cp S S'"
proof -
  have "cdcl_cp S S'" and "conflicting S' \<noteq> C_True" using cp cdcl_cp.intros by auto
  hence "cdcl_cp\<^sup>+\<^sup>+ S S'" by blast
  moreover have "no_step cdcl_cp S'"
    using \<open>conflicting S' \<noteq> C_True\<close> by (metis cdcl_cp_conflicting_not_empty
      conflicting_clause.exhaust)
  ultimately show "full cdcl_cp S S'" unfolding full_def by blast+
qed

lemma cdcl_cp_fst_empty_conflicting_false:
  assumes "cdcl_cp S S'"
  and "trail S = []"
  and "conflicting S \<noteq> C_True"
  shows False
  using assms by (induct rule: cdcl_cp.induct) auto

lemma cdcl_o_fst_empty_conflicting_false:
  assumes "cdcl_o S S'"
  and "trail S = []"
  and "conflicting S \<noteq> C_True"
  shows False
  using assms by (induct rule: cdcl_o_induct) auto

lemma cdcl_s_fst_empty_conflicting_false:
  assumes "cdcl_s S S'"
  and "trail S = []"
  and "conflicting S \<noteq> C_True"
  shows False
  using assms apply (induct rule: cdcl_s.induct)
  using tranclpD cdcl_cp_fst_empty_conflicting_false unfolding full_def apply fast
  using cdcl_o_fst_empty_conflicting_false by blast
thm cdcl_cp.induct[split_format(complete)]

lemma cdcl_cp_conflicting_is_false:
  "cdcl_cp S S' \<Longrightarrow> conflicting S = C_Clause {#} \<Longrightarrow> False"
  by (induction rule: cdcl_cp.induct) (auto elim!: conflictE propagateE)

lemma rtranclp_cdcl_cp_conflicting_is_false:
  "cdcl_cp\<^sup>+\<^sup>+ S S' \<Longrightarrow>  conflicting S = C_Clause {#} \<Longrightarrow> False"
  apply (induction rule: tranclp.induct)
  by (auto dest: cdcl_cp_conflicting_is_false)

lemma cdcl_o_conflicting_is_false:
  "cdcl_o S S' \<Longrightarrow>  conflicting S = C_Clause {#} \<Longrightarrow> False"
  by (induction rule: cdcl_o_induct) auto


lemma cdcl_s_conflicting_is_false:
  "cdcl_s S S' \<Longrightarrow>  conflicting S = C_Clause {#} \<Longrightarrow> False"
  apply (induction rule: cdcl_s.induct)
    unfolding full_def apply (metis (no_types) cdcl_cp_conflicting_not_empty tranclpD)
  unfolding full0_def by (metis conflict_with_false_implies_terminated other)

lemma rtranclp_cdcl_s_conflicting_is_false:
  "cdcl_s\<^sup>*\<^sup>* S S' \<Longrightarrow> conflicting S = C_Clause {#} \<Longrightarrow> S' = S"
  apply (induction rule: rtranclp.induct)
    apply simp
  using cdcl_s_conflicting_is_false by blast

(*TODO Move*)
lemma conflicting_clause_full0_cdcl_cp:
  "conflicting S \<noteq> C_True \<Longrightarrow> full0 cdcl_cp S S"
unfolding full0_def rtranclp_unfold tranclp_unfold by (auto simp add: cdcl_cp.simps)

lemma skip_unique:
  "skip S T \<Longrightarrow> skip S T' \<Longrightarrow> T = T'"
  by (auto simp: st_equal elim!:skipE)

lemma resolve_unique:
  "resolve S T \<Longrightarrow> resolve S T' \<Longrightarrow> T = T'"
  by (auto elim!: resolveE)

lemma full0_cdcl_init_clss_with_false_normal_form:
  assumes
    "\<forall> m\<in> set M. \<not>is_marked m" and
    "E = C_Clause D" and
    "state S = (M, N, U, 0, E)"
    "full0 cdcl_s S S'" and
    "all_decomposition_implies (init_clss S)
      (get_all_marked_decomposition (trail S))"
    "cdcl_learned_clause S"
    "cdcl_M_level_inv S"
    "no_strange_atm S"
    "distinct_cdcl_state S"
    "cdcl_conflicting S"
  shows "\<exists>M''. state S' = (M'', N, U, 0, C_Clause {#})"
  using assms(10,9,8,7,6,5,4,3,2,1)
proof (induction M arbitrary: E D S)
  case Nil
  thus ?case
    using rtranclp_cdcl_s_conflicting_is_false unfolding full0_def cdcl_conflicting_def by auto
next
  case (Cons L M) note IH = this(1) and full = this(8) and E = this(10) and inv = this(2-7) and
    S = this(9) and nm = this(11)
  let ?S' = "update_trail (L # trail S) S"
  obtain K p where K: "L = Propagated K p"
    using nm by (cases L) auto
  have "every_mark_is_a_conflict S" using inv unfolding cdcl_conflicting_def by auto
  hence MpK: "M \<Turnstile>as CNot (cls_of_mark p - {#K#})" and Kp: "K \<in># cls_of_mark p"
    using S unfolding K by fastforce+
  hence p: "cls_of_mark p = (cls_of_mark p - {#K#}) + {#K#}"
    by (auto simp add: multiset_eq_iff)
  hence K': "L = Propagated K (mark_of_cls ((cls_of_mark p - {#K#}) + {#K#}))"
    using K by auto

  consider (D) "D = {#}" | (D') "D \<noteq> {#}" by blast
  thus ?case
    proof cases
      case (D)
      thus ?thesis
        using full rtranclp_cdcl_s_conflicting_is_false S unfolding full0_def E D by auto
    next
      case (D')
      hence no_p: "no_step propagate S" and no_c: "no_step conflict S"
        using S E by auto
      hence "no_step cdcl_cp S" by (auto simp: cdcl_cp.simps)
      have res_skip: "\<exists>T. (resolve S T \<and> no_step skip S \<and> full0 cdcl_cp T T)
        \<or> (skip S T \<and> no_step resolve S \<and> full0 cdcl_cp T T)"
        proof cases
          assume "-lit_of L \<notin># D"
          then obtain T where sk: "skip S T" and res: "no_step resolve S"
            using D' S unfolding skip.simps K E  by fastforce
          have "full0 cdcl_cp T T"
            using sk by (auto simp add: conflicting_clause_full0_cdcl_cp)
          thus ?thesis
            using sk res by blast
        next
          assume LD: "\<not>-lit_of L \<notin># D"
          hence D: "C_Clause D = C_Clause ((D - {#-lit_of L#}) + {#-lit_of L#})"
            by (auto simp add: multiset_eq_iff)

          have "\<And>L. get_level L M = 0"
            by (simp add: nm)
          then have "get_maximum_level (D - {#- K#})
            (Propagated K (mark_of_cls (cls_of_mark p - {#K#} + {#K#})) # M) = 0"
            using  LD get_maximum_level_exists_lit_of_max_level
            proof -
              obtain L' where "get_level L' (L#M) = get_maximum_level D (L#M)"
                using  LD get_maximum_level_exists_lit_of_max_level[of D "L#M"] by fastforce
              thus ?thesis by (metis (mono_tags) K' bex_msetE get_level_skip_all_not_marked
                get_maximum_level_exists_lit nm not_gr0)
            qed
          then obtain T where sk: "resolve S T" and res: "no_step skip S"
            using resolving[of S K "cls_of_mark p - {#K#}" M N U 0 "(D - {#-K#})"] S unfolding K' D E
            by fastforce
          have "full0 cdcl_cp T T"
            using sk by (auto simp add: conflicting_clause_full0_cdcl_cp)
          thus ?thesis
           using sk res by blast
        qed
      hence step_s: "\<exists>T. cdcl_s S T"
        using \<open>no_step cdcl_cp S\<close> other' by blast
      have "get_all_marked_decomposition (L # M) = [([], L#M)]"
        using nm unfolding K apply (induction M rule: marked_lit_list_induct, simp)
          by (case_tac "hd (get_all_marked_decomposition xs)", auto)+
      hence no_b: "no_step backtrack S"
        using nm S by (auto elim!: backtrackE)
      have no_d: "no_step decided S"
        using S E by auto

      have full0: "full0 cdcl_cp S S"
        using S E by (auto simp add: conflicting_clause_full0_cdcl_cp)
      hence no_f: "no_step (full cdcl_cp) S"
        unfolding full0_def full_def rtranclp_unfold by (meson tranclpD)
      obtain T where
        s: "cdcl_s S T" and st: "cdcl_s\<^sup>*\<^sup>* T S'"
        using full step_s unfolding full0_def by (metis E Nitpick.rtranclp_unfold tranclpD)
      have "resolve S T \<or> skip S T"
        using s no_b no_d res_skip full0  unfolding cdcl_s.simps cdcl_o.simps full0_unfold full_def
        by (metis (no_types, hide_lams) cdcl_bj.cases resolve_unique skip_unique tranclpD)
      then obtain D' where T: "state T = (M, N, U, 0, C_Clause D')"
        using S E by auto

      have st_c: "cdcl\<^sup>*\<^sup>* S T"
        using E T rtranclp_cdcl_s_rtranclp_cdcl s by blast
      have "cdcl_conflicting T"
        using rtranclp_cdcl_all_inv(6)[OF st_c  inv(6,5,4,3,2,1)]  .
      show ?thesis
        apply (rule IH[of T])
                  using rtranclp_cdcl_all_inv(6)[OF st_c inv(6,5,4,3,2,1)] apply blast
                using rtranclp_cdcl_all_inv(5)[OF st_c inv(6,5,4,3,2,1)] apply blast
               using rtranclp_cdcl_all_inv(4)[OF st_c inv(6,5,4,3,2,1)] apply blast
              using rtranclp_cdcl_all_inv(3)[OF st_c inv(6,5,4,3,2,1)] apply blast
             using rtranclp_cdcl_all_inv(2)[OF st_c inv(6,5,4,3,2,1)] apply blast
            using rtranclp_cdcl_all_inv(1)[OF st_c inv(6,5,4,3,2,1)] apply blast
           apply (metis full full0_def st)
          using T E apply blast
         apply auto[]
        using nm by simp
    qed
qed

lemma full_cdcl_s_normal_forms_is_one_false:
  fixes S' :: "'st"
  assumes full: "full0 cdcl_s (init_state N) S'"
  and no_d: "distinct_mset_set N"
  and finite[simp]: "finite N"
  and empty: "{#} \<in> N"
  shows "conflicting S' = C_Clause {#} \<and> unsatisfiable (init_clss S')"
proof -
  let ?S = "init_state N"
  have "cdcl_s\<^sup>*\<^sup>* ?S S'" and "no_step cdcl_s S'" using full unfolding full0_def by auto
  hence plus_or_eq: "cdcl_s\<^sup>+\<^sup>+ ?S S' \<or> S' = ?S" unfolding rtranclp_unfold by auto
  have "\<exists>S''. conflict ?S S''" using empty by (auto simp add: conflict.simps)
  hence cdcl_s: "\<exists>S'. cdcl_s ?S S'"
    using cdcl_cp.conflict'[of ?S] conflict_is_full_cdcl_cp cdcl_s.intros(1) by metis
  have "S' \<noteq> ?S"  using \<open>no_step cdcl_s S'\<close> cdcl_s by blast

  then obtain St:: 'st where St: "cdcl_s ?S St" and "cdcl_s\<^sup>*\<^sup>* St S'"
    using plus_or_eq by (metis (no_types) \<open>cdcl_s\<^sup>*\<^sup>* ?S S'\<close> converse_rtranclpE)
  have st: "cdcl\<^sup>*\<^sup>* ?S St"
    by (simp add: Nitpick.rtranclp_unfold \<open>cdcl_s ?S St\<close> cdcl_s_tranclp_cdcl)

  have "\<exists>T. conflict ?S T"
    using empty by (auto simp add: conflict.simps)
  hence fullSt: "full cdcl_cp ?S St"
    using St unfolding cdcl_s.simps by blast
  then have bt: "backtrack_lvl St = (0::nat)"
    using rtranclp_cdcl_cp_backtrack_lvl tranclp_into_rtranclp unfolding full_def by fastforce
  have cls_St: "init_clss St = N"
    using fullSt  cdcl_s_no_more_init_clss[OF St] by auto
  have "conflicting St \<noteq> C_True"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "\<exists>T. conflict St T"
        using empty cls_St by (auto simp: conflict.simps clauses_def)
      thus False using fullSt unfolding full_def by blast
    qed

  have 1: "\<forall>m\<in>set (trail St). \<not> is_marked m"
    using fullSt unfolding full_def by (auto dest!: tranclp_into_rtranclp
      rtranclp_cdcl_cp_dropWhile_trail)
  have 2: "full0 cdcl_s St S'"
    using \<open>cdcl_s\<^sup>*\<^sup>* St S'\<close> \<open>no_step cdcl_s S'\<close> bt unfolding full0_def by auto
  have 3: "all_decomposition_implies
      (init_clss St)
      (get_all_marked_decomposition
         (trail St))"
   using rtranclp_cdcl_all_inv(1)[OF st] finite no_d bt by simp
  have 4: "cdcl_learned_clause St"
    using rtranclp_cdcl_all_inv(2)[OF st] finite no_d bt bt by simp
  have 5: "cdcl_M_level_inv St"
    using rtranclp_cdcl_all_inv(3)[OF st] finite no_d bt by simp
  have 6: "no_strange_atm St"
    using rtranclp_cdcl_all_inv(4)[OF st] finite no_d bt by simp
  have 7: "distinct_cdcl_state St"
    using rtranclp_cdcl_all_inv(5)[OF st] finite no_d bt by simp
  have 8: "cdcl_conflicting St"
    using rtranclp_cdcl_all_inv(6)[OF st] finite no_d bt by simp
  have "init_clss S' = init_clss St" and "conflicting S' = C_Clause {#}"
    using \<open>conflicting St \<noteq> C_True\<close> full0_cdcl_init_clss_with_false_normal_form[OF 1, of _ _ St _ _
      S'] 2 3 4 5 6 7 8 St
    apply (metis \<open>cdcl_s\<^sup>*\<^sup>* St S'\<close> cdcl_cw_ops.rtranclp_cdcl_s_no_more_init_clss cdcl_cw_ops_axioms)
    using \<open>conflicting St \<noteq> C_True\<close> full0_cdcl_init_clss_with_false_normal_form[OF 1, of _ _ St _ _
      S']
    2 3 4 5 6 7 8 by (metis bt conflicting_clause.exhaust prod.inject)

  moreover have "init_clss S' = N"
    using \<open>cdcl_s\<^sup>*\<^sup>* (init_state N) S'\<close> rtranclp_cdcl_s_no_more_init_clss by fastforce
  moreover have "unsatisfiable N" by (meson empty satisfiable_carac true_cls_empty true_clss_def)
  ultimately show ?thesis by auto
qed

(** prop 2.10.9*)
lemma full_cdcl_s_normal_forms:
  fixes S' :: 'st
  assumes full: "full0 cdcl_s (init_state N) S'"
  and no_d: "distinct_mset_set N"
  and finite: "finite N"
  shows "(conflicting S' = C_Clause {#} \<and> unsatisfiable (init_clss S'))
    \<or> (conflicting S' = C_True \<and> trail S' \<Turnstile>as init_clss S')"
  using assms full_cdcl_s_normal_forms_is_one_false full_cdcl_s_normal_forms_non_false by blast

lemma full_cdcl_s_normal_forms':
  fixes S' :: "'st"
  assumes full: "full0 cdcl_s (init_state N) S'"
  and no_d: "distinct_mset_set N"
  and finite[simp]: "finite N"
  shows "(conflicting S' = C_Clause {#} \<and> unsatisfiable (init_clss S'))
    \<or> (conflicting S' = C_True \<and> trail S' \<Turnstile>as init_clss S' \<and> satisfiable (init_clss S'))"
proof -
  consider
      (confl) "conflicting S' = C_Clause {#}" and "unsatisfiable (init_clss S')"
    | (sat) "conflicting S' = C_True" and "trail S' \<Turnstile>as init_clss S'"
    using full_cdcl_s_normal_forms[OF assms] by auto
  thus ?thesis
    proof cases
      case confl
      thus ?thesis by auto
    next
      case sat
      have "cdcl_M_level_inv (init_state N)" by auto
      hence "cdcl_M_level_inv S'"
        using full rtranclp_cdcl_s_consistent_inv unfolding full0_def by blast
      hence "consistent_interp (lits_of (trail S'))" unfolding cdcl_M_level_inv_def by blast
      moreover have "lits_of (trail S') \<Turnstile>s init_clss S'"
        using sat(2) by (auto simp add: true_annots_def true_annot_def true_clss_def)
      ultimately have "satisfiable (init_clss S')" by simp
      thus ?thesis using sat by blast
    qed
qed
end
end