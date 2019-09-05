theory IsaSAT_Trail
imports IsaSAT_Literals

begin


subsubsection \<open>Trail\<close>

text \<open>Our trail contains several additional information compared to the simple trail:
  \<^item> the (reversed) trail in an array (i.e., the trail in the same order as presented in
  ``Automated Reasoning'');
  \<^item> the mapping from any \<^emph>\<open>literal\<close> (and not an atom) to its polarity;
  \<^item> the mapping from a \<^emph>\<open>atom\<close> to its level or reason (in two different arrays);
  \<^item> the current level of the state;
  \<^item> the control stack.

We copied the idea from the mapping from a literals to it polarity instead of an atom to its
polarity from a comment by Armin Biere in CaDiCal. We only observed a (at best) faint
performance increase, but as it seemed slightly faster and does not increase the length of the
formalisation, we kept it.

The control stack is the latest addition: it contains the positions of the decisions in the trail.
It is mostly to enable fast restarts (since it allows to directly iterate over all decision of the
trail), but might also slightly speed up backjumping (since we know how far we are going back in the
trail). Remark that the control stack contains is not updated during the backjumping, but only
\<^emph>\<open>after\<close> doing it (as we keep only the the beginning of it).
\<close>


paragraph \<open>Polarities\<close>

type_synonym tri_bool = \<open>bool option\<close>

definition UNSET :: \<open>tri_bool\<close> where
  [simp]: \<open>UNSET = None\<close>

definition SET_FALSE :: \<open>tri_bool\<close> where
  [simp]: \<open>SET_FALSE = Some False\<close>

definition SET_TRUE :: \<open>tri_bool\<close> where
  [simp]: \<open>SET_TRUE = Some True\<close>

definition (in -) tri_bool_eq :: \<open>tri_bool \<Rightarrow> tri_bool \<Rightarrow> bool\<close> where
  \<open>tri_bool_eq = (=)\<close>


  
paragraph \<open>Types\<close>

type_synonym trail_pol =
   \<open>nat literal list \<times> tri_bool list \<times> nat list \<times> nat list \<times> nat \<times> nat list\<close>

definition get_level_atm where
  \<open>get_level_atm M L = get_level M (Pos L)\<close>

definition polarity_atm where
  \<open>polarity_atm M L =
    (if Pos L \<in> lits_of_l M then SET_TRUE
    else if Neg L \<in> lits_of_l M then SET_FALSE
    else None)\<close>

definition defined_atm :: \<open>('v, nat) ann_lits \<Rightarrow> 'v \<Rightarrow> bool\<close> where
\<open>defined_atm M L = defined_lit M (Pos L)\<close>

abbreviation undefined_atm where
  \<open>undefined_atm M L \<equiv> \<not>defined_atm M L\<close>


paragraph \<open>Control Stack\<close>

inductive control_stack where
empty:
  \<open>control_stack [] []\<close> |
cons_prop:
  \<open>control_stack cs M \<Longrightarrow> control_stack cs (Propagated L C # M)\<close> |
cons_dec:
  \<open>control_stack cs M \<Longrightarrow> n = length M \<Longrightarrow> control_stack (cs @ [n]) (Decided L # M)\<close>

inductive_cases control_stackE: \<open>control_stack cs M\<close>

lemma control_stack_length_count_dec:
  \<open>control_stack cs M \<Longrightarrow> length cs = count_decided M\<close>
  by (induction rule: control_stack.induct) auto

lemma control_stack_le_length_M:
  \<open>control_stack cs M \<Longrightarrow> c\<in>set cs \<Longrightarrow> c < length M\<close>
  by (induction rule: control_stack.induct) auto

lemma control_stack_propa[simp]:
  \<open>control_stack cs (Propagated x21 x22 # list) \<longleftrightarrow> control_stack cs list\<close>
  by (auto simp: control_stack.intros elim: control_stackE)

lemma control_stack_filter_map_nth:
  \<open>control_stack cs M \<Longrightarrow> filter is_decided (rev M) = map (nth (rev M)) cs\<close>
  apply (induction rule: control_stack.induct)
  subgoal by auto
  subgoal for cs M L C
    using control_stack_le_length_M[of cs M]
    by (auto simp: nth_append)
  subgoal for cs M L
    using control_stack_le_length_M[of cs M]
    by (auto simp: nth_append)
  done

lemma control_stack_empty_cs[simp]: \<open>control_stack [] M \<longleftrightarrow> count_decided M = 0\<close>
  by (induction M rule:ann_lit_list_induct)
    (auto simp: control_stack.empty control_stack.cons_prop elim: control_stackE)

text \<open>This is an other possible definition. It is not inductive, which makes it easier to reason
about appending (or removing) some literals from the trail. It is however much less clear if the
definition is correct.\<close>
definition control_stack' where
  \<open>control_stack' cs M \<longleftrightarrow>
     (length cs = count_decided M \<and>
       (\<forall>L\<in>set M. is_decided L \<longrightarrow> (cs ! (get_level M (lit_of L) - 1) < length M \<and>
          rev M!(cs ! (get_level M (lit_of L) - 1)) = L)))\<close>

lemma control_stack_rev_get_lev:
  \<open>control_stack cs M  \<Longrightarrow>
    no_dup M \<Longrightarrow> L\<in>set M \<Longrightarrow> is_decided L \<Longrightarrow> rev M!(cs ! (get_level M (lit_of L) - 1)) = L\<close>
  apply (induction arbitrary: L rule: control_stack.induct)
  subgoal by auto
  subgoal for cs M L C La
    using control_stack_le_length_M[of cs M] control_stack_length_count_dec[of cs M]
      count_decided_ge_get_level[of M \<open>lit_of La\<close>]
    apply (auto simp: get_level_cons_if nth_append atm_of_eq_atm_of undefined_notin)
    by (metis Suc_count_decided_gt_get_level Suc_less_eq Suc_pred count_decided_0_iff diff_is_0_eq
        le_SucI le_refl neq0_conv nth_mem)
  subgoal for cs M L
    using control_stack_le_length_M[of cs M] control_stack_length_count_dec[of cs M]
    apply (auto simp: nth_append get_level_cons_if atm_of_eq_atm_of undefined_notin)
    by (metis Suc_count_decided_gt_get_level Suc_less_eq Suc_pred count_decided_0_iff diff_is_0_eq
        le_SucI le_refl neq0_conv)+
  done

lemma control_stack_alt_def_imp:
  \<open>no_dup M \<Longrightarrow> (\<And>L. L \<in>set M \<Longrightarrow> is_decided L \<Longrightarrow> cs ! (get_level M (lit_of L) - 1) < length M \<and>
        rev M!(cs ! (get_level M (lit_of L) - 1)) = L) \<Longrightarrow>
    length cs = count_decided M \<Longrightarrow>
    control_stack cs M\<close>
proof (induction M arbitrary: cs rule:ann_lit_list_induct)
  case Nil
  then show ?case by auto
next
  case (Decided L M) note IH = this(1) and n_d = this(2) and dec = this(3) and length = this(4)
  from length obtain cs' n where cs[simp]: \<open>cs = cs' @ [n]\<close>
    using length by (cases cs rule: rev_cases) auto
  have [simp]: \<open>rev M ! n \<in> set M \<Longrightarrow> is_decided (rev M ! n) \<Longrightarrow> count_decided M \<noteq> 0\<close>
    by (auto simp: count_decided_0_iff)
  have dec': \<open>L'\<in>set M \<Longrightarrow> is_decided L' \<Longrightarrow> cs' ! (get_level M (lit_of L') - 1) < length M \<and>
        rev M ! (cs' ! (get_level M (lit_of L') - 1)) = L'\<close> for L'
    using dec[of L'] n_d length
    count_decided_ge_get_level[of M \<open>lit_of L'\<close>]
    apply (auto simp: get_level_cons_if atm_of_eq_atm_of undefined_notin
        split: if_splits)
    apply (auto simp: nth_append split: if_splits)
    done
  have le: \<open>length cs' = count_decided M\<close>
    using length by auto
  have [simp]: \<open>n = length M\<close>
    using n_d dec[of \<open>Decided L\<close>] le undefined_notin[of M \<open>rev M ! n\<close>] nth_mem[of n \<open>rev M\<close>]
    by (auto simp: nth_append split: if_splits)
  show ?case
    unfolding cs
    apply (rule control_stack.cons_dec)
    subgoal
      apply (rule IH)
      using n_d dec' le by auto
    subgoal by auto
    done
next
  case (Propagated L m M) note IH = this(1) and n_d = this(2) and dec = this(3) and length = this(4)
  have [simp]: \<open>rev M ! n \<in> set M \<Longrightarrow> is_decided (rev M ! n) \<Longrightarrow> count_decided M \<noteq> 0\<close> for n
    by (auto simp: count_decided_0_iff)
  have dec': \<open>L'\<in>set M \<Longrightarrow> is_decided L' \<Longrightarrow> cs ! (get_level M (lit_of L') - 1) < length M \<and>
        rev M ! (cs ! (get_level M (lit_of L') - 1)) = L'\<close> for L'
    using dec[of L'] n_d length
    count_decided_ge_get_level[of M \<open>lit_of L'\<close>]
    apply (cases L')
    apply (auto simp: get_level_cons_if atm_of_eq_atm_of undefined_notin
        split: if_splits)
    apply (auto simp: nth_append split: if_splits)
    done
  show ?case
    apply (rule control_stack.cons_prop)
    apply (rule IH)
    subgoal using n_d by auto
    subgoal using dec' by auto
    subgoal using length by auto
    done
qed

lemma control_stack_alt_def: \<open>no_dup M \<Longrightarrow> control_stack' cs M \<longleftrightarrow> control_stack cs M\<close>
  using control_stack_alt_def_imp[of M cs] control_stack_rev_get_lev[of cs M]
    control_stack_length_count_dec[of cs M] control_stack_le_length_M[of cs M]
  unfolding control_stack'_def apply -
  apply (rule iffI)
  subgoal by blast
  subgoal
    using count_decided_ge_get_level[of M]
    by (metis One_nat_def Suc_count_decided_gt_get_level Suc_less_eq Suc_pred count_decided_0_iff
        less_imp_diff_less neq0_conv nth_mem)
  done

lemma control_stack_decomp:
  assumes
    decomp: \<open>(Decided L # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    cs: \<open>control_stack cs M\<close> and
    n_d: \<open>no_dup M\<close>
  shows \<open>control_stack (take (count_decided M1) cs) M1\<close>
proof -
  obtain M3 where M: \<open>M = M3 @ M2 @ Decided L # M1\<close>
    using decomp by auto
  define M2' where \<open>M2' = M3 @ M2\<close>
  have M: \<open>M = M2' @ Decided L # M1\<close>
    unfolding M M2'_def by auto
  have n_d1: \<open>no_dup M1\<close>
    using n_d no_dup_appendD unfolding M by auto
  have \<open>control_stack' cs M\<close>
    using cs
    apply (subst (asm) control_stack_alt_def[symmetric])
     apply (rule n_d)
    apply assumption
    done
  then have
    cs_M: \<open>length cs = count_decided M\<close> and
    L: \<open>\<And>L. L\<in>set M \<Longrightarrow> is_decided L \<Longrightarrow>
      cs ! (get_level M (lit_of L) - 1) < length M \<and> rev M ! (cs ! (get_level M (lit_of L) - 1)) = L\<close>
    unfolding control_stack'_def by auto
  have H: \<open>L' \<in> set M1 \<Longrightarrow> undefined_lit M2' (lit_of L') \<and> atm_of (lit_of L') \<noteq> atm_of L\<close>  for L'
    using n_d unfolding M
    by (metis atm_of_eq_atm_of defined_lit_no_dupD(1) defined_lit_uminus lit_of.simps(1)
        no_dup_appendD no_dup_append_cons no_dup_cons undefined_notin)
  have \<open>distinct M\<close>
    using no_dup_imp_distinct[OF n_d] .
  then have K: \<open>L' \<in> set M1 \<Longrightarrow> x < length M \<Longrightarrow> rev M ! x = L' \<Longrightarrow> x < length M1\<close> for x L'
    unfolding M apply (auto simp: nth_append nth_Cons split: if_splits nat.splits)
    by (metis length_rev less_diff_conv local.H not_less_eq nth_mem set_rev undefined_notin)
  have I: \<open>L \<in> set M1 \<Longrightarrow> is_decided L \<Longrightarrow> get_level M1 (lit_of L) > 0\<close> for L
    using n_d unfolding M by (auto dest!: split_list)
  have cs': \<open>control_stack' (take (count_decided M1) cs) M1\<close>
    unfolding control_stack'_def
    apply (intro conjI ballI impI)
    subgoal using cs_M unfolding M by auto
    subgoal for L using n_d L[of L] H[of L] K[of L \<open>cs ! (get_level M1 (lit_of L) - Suc 0)\<close>]
        count_decided_ge_get_level[of \<open>M1\<close> \<open>lit_of L\<close>] I[of L]
      unfolding M by auto
    subgoal for L using n_d L[of L] H[of L] K[of L \<open>cs ! (get_level M1 (lit_of L) - Suc 0)\<close>]
        count_decided_ge_get_level[of \<open>M1\<close> \<open>lit_of L\<close>] I[of L]
      unfolding M by auto
    done
  show ?thesis
    apply (subst control_stack_alt_def[symmetric])
     apply (rule n_d1)
    apply (rule cs')
    done
qed


paragraph \<open>Encoding of the reasons\<close>

definition DECISION_REASON :: nat where
  \<open>DECISION_REASON = 1\<close>

definition ann_lits_split_reasons where
  \<open>ann_lits_split_reasons \<A> = {((M, reasons), M'). M = map lit_of (rev M') \<and>
    (\<forall>L \<in> set M'. is_proped L \<longrightarrow>
        reasons ! (atm_of (lit_of L)) = mark_of L \<and> mark_of L \<noteq> DECISION_REASON) \<and>
    (\<forall>L \<in> set M'. is_decided L \<longrightarrow> reasons ! (atm_of (lit_of L)) = DECISION_REASON) \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. atm_of L < length reasons)
  }\<close>

definition trail_pol :: \<open>nat multiset \<Rightarrow> (trail_pol \<times> (nat, nat) ann_lits) set\<close> where
  \<open>trail_pol \<A> =
   {((M', xs, lvls, reasons, k, cs), M). ((M', reasons), M) \<in> ann_lits_split_reasons \<A> \<and>
    no_dup M \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. nat_of_lit L < length xs \<and> xs ! (nat_of_lit L) = polarity M L) \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. atm_of L < length lvls \<and> lvls ! (atm_of L) = get_level M L) \<and>
    k = count_decided M \<and>
    (\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<and>
    control_stack cs M \<and>
    isasat_input_bounded \<A>}\<close>


paragraph \<open>Definition of the full trail\<close>


lemma trail_pol_alt_def:
  \<open>trail_pol \<A> = {((M', xs, lvls, reasons, k, cs), M).
    ((M', reasons), M) \<in> ann_lits_split_reasons \<A> \<and>
    no_dup M \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. nat_of_lit L < length xs \<and> xs ! (nat_of_lit L) = polarity M L) \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. atm_of L < length lvls \<and> lvls ! (atm_of L) = get_level M L) \<and>
    k = count_decided M \<and>
    (\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<and>
    control_stack cs M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M \<and>
    length M < uint32_max \<and>
    length M \<le> uint32_max div 2 + 1 \<and>
    count_decided M < uint32_max \<and>
    length M' = length M \<and>
    M' = map lit_of (rev M) \<and>
    isasat_input_bounded \<A>
   }\<close>
proof -
  have [intro!]: \<open>length M < n \<Longrightarrow> count_decided M < n\<close> for M n
    using length_filter_le[of is_decided M]
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def uint32_max_def count_decided_def
        simp del: length_filter_le
        dest: length_trail_uint32_max_div2)
  show ?thesis
    unfolding trail_pol_def
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def uint32_max_def ann_lits_split_reasons_def
        dest: length_trail_uint32_max_div2
	simp del: isasat_input_bounded_def)
qed

paragraph \<open>Code generation\<close>

subparagraph \<open>Conversion between incomplete and complete mode\<close>

definition trail_fast_of_slow :: \<open>(nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>trail_fast_of_slow = id\<close>

definition trail_pol_slow_of_fast :: \<open>trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>trail_pol_slow_of_fast =
    (\<lambda>(M, val, lvls, reason, k, cs). (M, val, lvls, reason, k, cs))\<close>

definition trail_slow_of_fast :: \<open>(nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>trail_slow_of_fast = id\<close>

definition trail_pol_fast_of_slow :: \<open>trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>trail_pol_fast_of_slow =
    (\<lambda>(M, val, lvls, reason, k, cs). (M, val, lvls, reason, k, cs))\<close>

lemma trail_pol_slow_of_fast_alt_def:
  \<open>trail_pol_slow_of_fast M = M\<close>
  by (cases M)
    (auto simp: trail_pol_slow_of_fast_def)

lemma trail_pol_fast_of_slow_trail_fast_of_slow:
  \<open>(RETURN o trail_pol_fast_of_slow, RETURN o trail_fast_of_slow)
    \<in> [\<lambda>M. (\<forall>C L. Propagated L C \<in> set M \<longrightarrow> C < uint64_max)]\<^sub>f
        trail_pol \<A> \<rightarrow> \<langle>trail_pol \<A>\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: trail_pol_def trail_pol_fast_of_slow_def 
    trail_fast_of_slow_def)

lemma trail_pol_slow_of_fast_trail_slow_of_fast:
  \<open>(RETURN o trail_pol_slow_of_fast, RETURN o trail_slow_of_fast)
    \<in> trail_pol \<A> \<rightarrow>\<^sub>f \<langle>trail_pol \<A>\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: trail_pol_def trail_pol_fast_of_slow_def 
     trail_fast_of_slow_def trail_slow_of_fast_def
     trail_pol_slow_of_fast_def)

lemma trail_pol_same_length[simp]: \<open>(M', M) \<in> trail_pol \<A> \<Longrightarrow> length (fst M') = length M\<close>
  by (auto simp: trail_pol_alt_def)

definition counts_maximum_level where
  \<open>counts_maximum_level M C = {i. C \<noteq> None \<longrightarrow> i = card_max_lvl M (the C)}\<close>

lemma counts_maximum_level_None[simp]: \<open>counts_maximum_level M None = Collect (\<lambda>_. True)\<close>
  by (auto simp: counts_maximum_level_def)



subparagraph \<open>Level of a literal\<close>


definition get_level_atm_pol_pre where
  \<open>get_level_atm_pol_pre = (\<lambda>((M, xs, lvls, k), L). L < length lvls)\<close>

definition get_level_atm_pol :: \<open>trail_pol \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>get_level_atm_pol = (\<lambda>(M, xs, lvls, k) L. lvls ! L)\<close>

lemma get_level_atm_pol_pre:
  assumes
    \<open>Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and
    \<open>(M', M) \<in> trail_pol \<A>\<close>
  shows \<open>get_level_atm_pol_pre (M', L)\<close>
  using assms
  by (auto 5 5 simp: trail_pol_def nat_lit_rel_def
    br_def get_level_atm_pol_pre_def intro!: ext)

lemma (in -) get_level_get_level_atm: \<open>get_level M L = get_level_atm M (atm_of L)\<close>
  unfolding get_level_atm_def
  by (cases L) (auto simp: get_level_Neg_Pos)

definition get_level_pol where
  \<open>get_level_pol M L = get_level_atm_pol M (atm_of L)\<close>

definition get_level_pol_pre where
  \<open>get_level_pol_pre = (\<lambda>((M, xs, lvls, k), L). atm_of L < length lvls)\<close>

lemma get_level_pol_pre:
  assumes
    \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and
    \<open>(M', M) \<in> trail_pol \<A>\<close>
  shows \<open>get_level_pol_pre (M', L)\<close>
  using assms
  by (auto 5 5 simp: trail_pol_def nat_lit_rel_def
     br_def get_level_pol_pre_def intro!: ext)


lemma get_level_get_level_pol:
  assumes
    \<open>(M', M) \<in> trail_pol \<A>\<close> and \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
  shows \<open>get_level M L = get_level_pol M' L\<close>
  using assms
  by (auto simp: get_level_pol_def get_level_atm_pol_def trail_pol_def)


subparagraph \<open>Current level\<close>

definition (in -) count_decided_pol where
  \<open>count_decided_pol = (\<lambda>(_, _, _, _, k, _). k)\<close>

lemma count_decided_trail_ref:
  \<open>(RETURN o count_decided_pol, RETURN o count_decided) \<in> trail_pol \<A> \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: trail_pol_def count_decided_pol_def)


subparagraph \<open>Polarity\<close>

definition (in -) polarity_pol :: \<open>trail_pol \<Rightarrow> nat literal \<Rightarrow> bool option\<close> where
  \<open>polarity_pol = (\<lambda>(M, xs, lvls, k) L. do {
     xs ! (nat_of_lit L)
  })\<close>

definition polarity_pol_pre where
  \<open>polarity_pol_pre = (\<lambda>(M, xs, lvls, k) L. nat_of_lit L < length xs)\<close>

lemma polarity_pol_polarity:
  \<open>(uncurry (RETURN oo polarity_pol), uncurry (RETURN oo polarity)) \<in>
     [\<lambda>(M, L). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f trail_pol \<A> \<times>\<^sub>f Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
   (auto simp: trail_pol_def polarity_def polarity_pol_def
      dest!: multi_member_split)

lemma polarity_pol_pre:
  \<open>(M', M) \<in> trail_pol \<A> \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> polarity_pol_pre M' L\<close>
  by (auto simp: trail_pol_def polarity_def polarity_pol_def polarity_pol_pre_def
      dest!: multi_member_split)


subsection \<open>Length of the trail\<close>

definition (in -) isa_length_trail_pre where
  \<open>isa_length_trail_pre = (\<lambda> (M', xs, lvls, reasons, k, cs). length M' \<le> uint32_max)\<close>

definition (in -) isa_length_trail where
  \<open>isa_length_trail = (\<lambda> (M', xs, lvls, reasons, k, cs). length_uint32_nat M')\<close>

lemma isa_length_trail_pre:
  \<open>(M, M') \<in> trail_pol \<A> \<Longrightarrow> isa_length_trail_pre M\<close>
  by (auto simp: isa_length_trail_def trail_pol_alt_def isa_length_trail_pre_def)

lemma isa_length_trail_length_u:
  \<open>(RETURN o isa_length_trail, RETURN o length_uint32_nat) \<in> trail_pol \<A> \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: isa_length_trail_def trail_pol_alt_def
    intro!: ASSERT_leI)


subparagraph \<open>Consing elements\<close>

definition cons_trail_Propagated_tr_pre where
  \<open>cons_trail_Propagated_tr_pre = (\<lambda>((L, C), (M, xs, lvls, reasons, k)). nat_of_lit L < length xs \<and>
    nat_of_lit (-L) < length xs \<and> atm_of L < length lvls \<and> atm_of L < length reasons \<and> length M < uint32_max)\<close>

definition cons_trail_Propagated_tr :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> trail_pol \<Rightarrow> trail_pol nres\<close> where
  \<open>cons_trail_Propagated_tr = (\<lambda>L C (M', xs, lvls, reasons, k, cs). do {
     ASSERT(cons_trail_Propagated_tr_pre ((L, C), (M', xs, lvls, reasons, k, cs)));
     RETURN (M' @ [L], let xs = xs[nat_of_lit L := SET_TRUE] in xs[nat_of_lit (-L) := SET_FALSE],
      lvls[atm_of L := k], reasons[atm_of L:= C], k, cs)})\<close>

lemma in_list_pos_neg_notD: \<open>Pos (atm_of (lit_of La)) \<notin> lits_of_l bc \<Longrightarrow>
       Neg (atm_of (lit_of La)) \<notin> lits_of_l bc \<Longrightarrow>
       La \<in> set bc \<Longrightarrow> False\<close>
  by (metis Neg_atm_of_iff Pos_atm_of_iff lits_of_def rev_image_eqI)


lemma cons_trail_Propagated_tr_pre:
  assumes \<open>(M', M) \<in> trail_pol \<A>\<close> and
    \<open>undefined_lit M L\<close> and
    \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and
    \<open>C \<noteq> DECISION_REASON\<close>
  shows \<open>cons_trail_Propagated_tr_pre ((L, C), M')\<close>
  using assms
  by (auto simp: trail_pol_alt_def ann_lits_split_reasons_def uminus_\<A>\<^sub>i\<^sub>n_iff
       cons_trail_Propagated_tr_pre_def
    intro!: ext)


lemma cons_trail_Propagated_tr:
  \<open>(uncurry2 (cons_trail_Propagated_tr), uncurry2 (cons_trail_propagate_wl_D)) \<in>
   [\<lambda>((L, C), M). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> C \<noteq> DECISION_REASON]\<^sub>f
    Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trail_pol \<A> \<rightarrow> \<langle>trail_pol \<A>\<rangle>nres_rel\<close>
  unfolding cons_trail_Propagated_tr_def cons_trail_propagate_wl_D_def
  apply (intro frefI nres_relI)
  subgoal for x y
  using cons_trail_Propagated_tr_pre[of \<open>snd (x)\<close> \<open>snd (y)\<close> \<A> \<open>fst (fst y)\<close> \<open>snd (fst y)\<close>]
  unfolding uncurry_def
  apply refine_vcg
  subgoal by auto
  subgoal
    by (cases \<open>fst (fst y)\<close>)
      (auto simp add: trail_pol_def polarity_def cons_trail_propagate_wl_D_def uminus_lit_swap
        cons_trail_Propagated_tr_def Decided_Propagated_in_iff_in_lits_of_l nth_list_update'
        ann_lits_split_reasons_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
        uminus_\<A>\<^sub>i\<^sub>n_iff atm_of_eq_atm_of
      intro!: ASSERT_refine_right
      dest!: in_list_pos_neg_notD dest: pos_lit_in_atms_of neg_lit_in_atms_of dest!: multi_member_split
      simp del: nat_of_lit.simps)
  done
  done

lemma cons_trail_Propagated_tr2:
  \<open>(((L, C), M), ((L', C'), M')) \<in> Id \<times>\<^sub>f Id \<times>\<^sub>f trail_pol \<A> \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow>
      C \<noteq> DECISION_REASON \<Longrightarrow>
  cons_trail_Propagated_tr L C M
  \<le> \<Down> ({(M'', M'''). (M'', M''') \<in> trail_pol \<A> \<and> M''' = Propagated L C # M' \<and> no_dup M'''}) (cons_trail_propagate_wl_D L' C' M')\<close>
  using cons_trail_Propagated_tr[THEN fref_to_Down_curry2, of \<A> L' C' M' L C M]
  unfolding cons_trail_Propagated_tr_def cons_trail_propagate_wl_D_def
  using cons_trail_Propagated_tr_pre[of M M' \<A> L C]
  unfolding uncurry_def
  apply refine_vcg
  subgoal by auto
  subgoal
    by (auto simp: trail_pol_def)
  done


lemma undefined_lit_count_decided_uint32_max:
  assumes
    M_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and n_d: \<open>no_dup M\<close> and
    \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and \<open>undefined_lit M L\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>
  shows \<open>Suc (count_decided M) \<le> uint32_max\<close>
proof -
  have dist_atm_M: \<open>distinct_mset {#atm_of (lit_of x). x \<in># mset M#}\<close>
    using n_d by (metis distinct_mset_mset_distinct mset_map no_dup_def)
  have incl: \<open>atm_of `# lit_of `# mset (Decided L # M) \<subseteq># remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using assms dist_atm_M
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l lits_of_def no_dup_distinct
        atm_of_eq_atm_of)
  from size_mset_mono[OF this] have 1: \<open>count_decided M + 1 \<le> size (remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l \<A>))\<close>
    using length_filter_le[of is_decided M] unfolding uint32_max_def count_decided_def
    by (auto simp del: length_filter_le)
  have inj_on: \<open>inj_on nat_of_lit (set_mset (remdups_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)))\<close>
    by (auto simp: inj_on_def)
  have H: \<open>xa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> atm_of xa \<le> uint32_max div 2\<close> for xa
    using bounded
    by (cases xa) (auto simp: uint32_max_def)
  have \<open>remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<subseteq># mset [0..< 1 + (uint32_max div 2)]\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using H distinct_image_mset_inj[OF inj_on]
    by (force simp del: literal_of_nat.simps simp: distinct_mset_mset_set
        dest: le_neq_implies_less)+
  note _ = size_mset_mono[OF this]
  moreover have \<open>size (nat_of_lit `# remdups_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)) = size (remdups_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>))\<close>
    by simp
  ultimately have 2: \<open>size (remdups_mset (atm_of `# (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>))) \<le> 1 + uint32_max div 2\<close>
    by auto

  show ?thesis
    using 1 2 by (auto simp: uint32_max_def)

  from size_mset_mono[OF incl] have 1: \<open>length M + 1 \<le> size (remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l \<A>))\<close>
    unfolding uint32_max_def count_decided_def
    by (auto simp del: length_filter_le)
  with 2 have \<open>length M  \<le> uint32_max\<close>
    by auto
qed

lemma length_trail_uint32_max:
  assumes
    M_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and n_d: \<open>no_dup M\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>
  shows \<open>length M \<le> uint32_max\<close>
proof -
  have dist_atm_M: \<open>distinct_mset {#atm_of (lit_of x). x \<in># mset M#}\<close>
    using n_d by (metis distinct_mset_mset_distinct mset_map no_dup_def)
  have incl: \<open>atm_of `# lit_of `# mset M \<subseteq># remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using assms dist_atm_M
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l lits_of_def no_dup_distinct
        atm_of_eq_atm_of)

  have inj_on: \<open>inj_on nat_of_lit (set_mset (remdups_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)))\<close>
    by (auto simp: inj_on_def)
  have H: \<open>xa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> atm_of xa \<le> uint32_max div 2\<close> for xa
    using bounded
    by (cases xa) (auto simp: uint32_max_def)
  have \<open>remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<subseteq># mset [0..< 1 + (uint32_max div 2)]\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using H distinct_image_mset_inj[OF inj_on]
    by (force simp del: literal_of_nat.simps simp: distinct_mset_mset_set
        dest: le_neq_implies_less)+
  note _ = size_mset_mono[OF this]
  moreover have \<open>size (nat_of_lit `# remdups_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)) = size (remdups_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>))\<close>
    by simp
  ultimately have 2: \<open>size (remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l \<A>)) \<le> 1 + uint32_max div 2\<close>
    by auto
  from size_mset_mono[OF incl] have 1: \<open>length M \<le> size (remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l \<A>))\<close>
    unfolding uint32_max_def count_decided_def
    by (auto simp del: length_filter_le)
  with 2 show ?thesis
    by (auto simp: uint32_max_def)
qed


definition last_trail_pol_pre where
  \<open>last_trail_pol_pre = (\<lambda>(M, xs, lvls, reasons, k). atm_of (last M) < length reasons \<and> M \<noteq> [])\<close>

definition (in -) last_trail_pol :: \<open>trail_pol \<Rightarrow> (nat literal \<times> nat option)\<close> where
  \<open>last_trail_pol = (\<lambda>(M, xs, lvls, reasons, k).
      let r = reasons ! (atm_of (last M)) in
      (last M, if r = DECISION_REASON then None else Some r))\<close>


definition tl_trailt_tr :: \<open>trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>tl_trailt_tr = (\<lambda>(M', xs, lvls, reasons, k, cs).
    let L = last M' in
    (butlast M',
    let xs = xs[nat_of_lit L := None] in xs[nat_of_lit (-L) := None],
    lvls[atm_of L := 0],
    reasons, if reasons ! atm_of L = DECISION_REASON then k-1 else k,
      if reasons ! atm_of L = DECISION_REASON then butlast cs else cs))\<close>

definition tl_trailt_tr_pre where
  \<open>tl_trailt_tr_pre = (\<lambda>(M, xs, lvls, reason, k, cs). M \<noteq> [] \<and> nat_of_lit(last M) < length xs \<and>
        nat_of_lit(-last M) < length xs  \<and> atm_of (last M) < length lvls \<and>
        atm_of (last M) < length reason \<and>
        (reason ! atm_of (last M) = DECISION_REASON \<longrightarrow> k \<ge> 1 \<and> cs \<noteq> []))\<close>

lemma ann_lits_split_reasons_map_lit_of:
  \<open>((M, reasons), M') \<in> ann_lits_split_reasons \<A> \<Longrightarrow> M = map lit_of (rev M')\<close>
  by (auto simp: ann_lits_split_reasons_def)

lemma control_stack_dec_butlast:
  \<open>control_stack b (Decided x1 # M's) \<Longrightarrow> control_stack (butlast b) M's\<close>
  by (cases b rule: rev_cases) (auto dest: control_stackE)

lemma tl_trail_tr:
  \<open>((RETURN o tl_trailt_tr), (RETURN o tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>f trail_pol \<A> \<rightarrow> \<langle>trail_pol \<A>\<rangle>nres_rel\<close>
proof -
  show ?thesis
    apply (intro frefI nres_relI, rename_tac x y, case_tac \<open>y\<close>)
    subgoal by fast
    subgoal for M M' L M's
      unfolding trail_pol_def comp_def RETURN_refine_iff trail_pol_def Let_def
      apply clarify
      apply (intro conjI; clarify?; (intro conjI)?)
      subgoal
        by (auto simp: trail_pol_def polarity_atm_def tl_trailt_tr_def
            ann_lits_split_reasons_def Let_def)
      subgoal by (auto simp: trail_pol_def polarity_atm_def tl_trailt_tr_def)
      subgoal by (auto simp: polarity_atm_def tl_trailt_tr_def Let_def)
      subgoal
        by (cases \<open>lit_of L\<close>)
          (auto simp: polarity_def tl_trailt_tr_def Decided_Propagated_in_iff_in_lits_of_l
            uminus_lit_swap Let_def
            dest: ann_lits_split_reasons_map_lit_of)
      subgoal
        by (auto simp: polarity_atm_def tl_trailt_tr_def Let_def
           atm_of_eq_atm_of get_level_cons_if)
      subgoal
        by (auto simp: polarity_atm_def tl_trailt_tr_def
           atm_of_eq_atm_of get_level_cons_if Let_def
            dest!: ann_lits_split_reasons_map_lit_of)
      subgoal
        by (cases \<open>L\<close>)
          (auto simp: tl_trailt_tr_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff ann_lits_split_reasons_def
            dest: no_dup_consistentD)
      subgoal
        by (auto simp: tl_trailt_tr_def)
      subgoal
        by (cases \<open>L\<close>)
          (auto simp: tl_trailt_tr_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff ann_lits_split_reasons_def
            control_stack_dec_butlast
            dest: no_dup_consistentD)
      done
    done
qed

lemma tl_trailt_tr_pre:
  assumes \<open>M \<noteq> []\<close>
    \<open>(M', M) \<in> trail_pol \<A>\<close>
  shows \<open>tl_trailt_tr_pre M'\<close>
proof -
  have [simp]: \<open>x \<noteq> [] \<Longrightarrow> is_decided (last x) \<Longrightarrow> Suc 0 \<le> count_decided x\<close> for x
    by (cases x rule: rev_cases) auto
  show ?thesis
    using assms
    by (cases M; cases \<open>hd M\<close>)
     (auto simp: trail_pol_def ann_lits_split_reasons_def uminus_\<A>\<^sub>i\<^sub>n_iff
        rev_map[symmetric] hd_append hd_map  tl_trailt_tr_pre_def simp del: rev_map
        intro!: ext)
qed

definition tl_trail_propedt_tr :: \<open>trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>tl_trail_propedt_tr = (\<lambda>(M', xs, lvls, reasons, k, cs).
    let L = last M' in
    (butlast M',
    let xs = xs[nat_of_lit L := None] in xs[nat_of_lit (-L) := None],
    lvls[atm_of L := 0],
    reasons, k, cs))\<close>

definition tl_trail_propedt_tr_pre where
  \<open>tl_trail_propedt_tr_pre =
     (\<lambda>(M, xs, lvls, reason, k, cs). M \<noteq> [] \<and> nat_of_lit(last M) < length xs \<and>
        nat_of_lit(-last M) < length xs  \<and> atm_of (last M) < length lvls \<and>
        atm_of (last M) < length reason)\<close>

lemma tl_trail_propedt_tr_pre:
  assumes \<open>(M', M) \<in> trail_pol \<A>\<close> and
    \<open>M \<noteq> []\<close>
  shows \<open>tl_trail_propedt_tr_pre M'\<close>
  using assms
  unfolding trail_pol_def comp_def RETURN_refine_iff trail_pol_def Let_def
    tl_trail_propedt_tr_def tl_trail_propedt_tr_pre_def
  apply clarify
  apply (cases M; intro conjI; clarify?; (intro conjI)?)
  subgoal
    by (auto simp: trail_pol_def polarity_atm_def tl_trailt_tr_def
	ann_lits_split_reasons_def Let_def)
  subgoal
    by (auto simp: polarity_atm_def tl_trailt_tr_def
       atm_of_eq_atm_of get_level_cons_if Let_def
	dest!: ann_lits_split_reasons_map_lit_of)
  subgoal
    by (cases \<open>hd M\<close>)
      (auto simp: tl_trailt_tr_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff ann_lits_split_reasons_def
	dest: no_dup_consistentD)
  subgoal
    by (cases \<open>hd M\<close>)
      (auto simp: tl_trailt_tr_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff ann_lits_split_reasons_def
	control_stack_dec_butlast
	dest: no_dup_consistentD)
  subgoal
    by (cases \<open>hd M\<close>)
      (auto simp: tl_trailt_tr_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff ann_lits_split_reasons_def
	control_stack_dec_butlast
	dest: no_dup_consistentD)
  done


definition (in -) lit_of_hd_trail where
  \<open>lit_of_hd_trail M = lit_of (hd M)\<close>

definition (in -) lit_of_last_trail_pol where
  \<open>lit_of_last_trail_pol = (\<lambda>(M, _). last M)\<close>

lemma lit_of_last_trail_pol_lit_of_last_trail:
   \<open>(RETURN o lit_of_last_trail_pol, RETURN o lit_of_hd_trail) \<in>
         [\<lambda>S. S \<noteq> []]\<^sub>f trail_pol \<A> \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (auto simp: lit_of_hd_trail_def trail_pol_def lit_of_last_trail_pol_def
     ann_lits_split_reasons_def hd_map rev_map[symmetric] last_rev
      intro!: frefI nres_relI)

subparagraph \<open>Setting a new literal\<close>

definition cons_trail_Decided :: \<open>nat literal \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>cons_trail_Decided L M' = Decided L # M'\<close>

definition cons_trail_Decided_tr :: \<open>nat literal \<Rightarrow> trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>cons_trail_Decided_tr = (\<lambda>L (M', xs, lvls, reasons, k, cs). do{
    let n = length M' in
    (M' @ [L], let xs = xs[nat_of_lit L := SET_TRUE] in xs[nat_of_lit (-L) := SET_FALSE],
      lvls[atm_of L := k+1], reasons[atm_of L := DECISION_REASON], k+1, cs @ [n])})\<close>

definition cons_trail_Decided_tr_pre where
  \<open>cons_trail_Decided_tr_pre =
    (\<lambda>(L, (M, xs, lvls, reason, k, cs)). nat_of_lit L < length xs \<and> nat_of_lit (-L) < length xs \<and>
      atm_of L < length lvls \<and> atm_of L < length reason  \<and> length cs < uint32_max \<and>
      Suc k \<le> uint32_max \<and> length M < uint32_max)\<close>

lemma length_cons_trail_Decided[simp]:
  \<open>length (cons_trail_Decided L M) = Suc (length M)\<close>
  by (auto simp: cons_trail_Decided_def)

lemma cons_trail_Decided_tr:
  \<open>(uncurry (RETURN oo cons_trail_Decided_tr), uncurry (RETURN oo cons_trail_Decided)) \<in>
  [\<lambda>(L, M). undefined_lit M L \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f Id \<times>\<^sub>f trail_pol \<A> \<rightarrow> \<langle>trail_pol \<A>\<rangle>nres_rel\<close>
  by (intro frefI nres_relI, rename_tac x y, case_tac \<open>fst x\<close>)
    (auto simp: trail_pol_def polarity_def cons_trail_Decided_def uminus_lit_swap
        Decided_Propagated_in_iff_in_lits_of_l
        cons_trail_Decided_tr_def nth_list_update' ann_lits_split_reasons_def
      dest!: in_list_pos_neg_notD multi_member_split
      intro: control_stack.cons_dec
      simp del: nat_of_lit.simps)

lemma cons_trail_Decided_tr_pre:
  assumes \<open>(M', M) \<in> trail_pol \<A>\<close> and
    \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and \<open>undefined_lit M L\<close>
  shows \<open>cons_trail_Decided_tr_pre (L, M')\<close>
  using assms
  by (auto simp: trail_pol_alt_def image_image ann_lits_split_reasons_def uminus_\<A>\<^sub>i\<^sub>n_iff
         cons_trail_Decided_tr_pre_def control_stack_length_count_dec
       intro!: ext undefined_lit_count_decided_uint32_max length_trail_uint32_max)


subparagraph \<open>Polarity: Defined or Undefined\<close>

definition (in -) defined_atm_pol_pre where
  \<open>defined_atm_pol_pre = (\<lambda>(M, xs, lvls, k) L. 2*L < length xs \<and>
      2*L \<le> uint32_max)\<close>

definition (in -) defined_atm_pol where
  \<open>defined_atm_pol = (\<lambda>(M, xs, lvls, k) L. \<not>((xs!(2*L)) = None))\<close>

lemma undefined_atm_code:
  \<open>(uncurry (RETURN oo defined_atm_pol), uncurry (RETURN oo defined_atm)) \<in>
   [\<lambda>(M, L). Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f trail_pol \<A> \<times>\<^sub>r Id \<rightarrow> \<langle>bool_rel\<rangle> nres_rel\<close>  (is ?A) and
  defined_atm_pol_pre:
    \<open>(M', M) \<in> trail_pol \<A> \<Longrightarrow> L \<in>#  \<A> \<Longrightarrow> defined_atm_pol_pre M' L\<close>
proof -
  have H: \<open>2*L < length xs\<close> (is \<open>?length\<close>) and
    none: \<open>defined_atm M L \<longleftrightarrow> xs ! (2*L) \<noteq> None\<close> (is ?undef) and
    le: \<open>2*L \<le> uint32_max\<close> (is ?le)
    if L_N: \<open>Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and tr: \<open>((M', xs, lvls, k), M) \<in> trail_pol \<A>\<close>
    for M xs lvls k M' L
  proof -
    have
       \<open>M' = map lit_of (rev M)\<close> and
       \<open>\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l \<A>. nat_of_lit L < length xs \<and> xs ! nat_of_lit L = polarity M L\<close>
      using tr unfolding trail_pol_def ann_lits_split_reasons_def by fast+
    then have L: \<open>nat_of_lit (Pos L) < length xs\<close> and
      xsL: \<open>xs ! (nat_of_lit (Pos L)) = polarity M (Pos L)\<close>
      using L_N by (auto dest!: multi_member_split)
    show ?length
      using L by simp
    show ?undef
      using xsL by (auto simp: polarity_def defined_atm_def
          Decided_Propagated_in_iff_in_lits_of_l split: if_splits)
    show \<open>2*L \<le> uint32_max\<close>
      using tr L_N unfolding trail_pol_def by auto
  qed
  show ?A
    unfolding defined_atm_pol_def
    by (intro frefI nres_relI) (auto 5 5 simp: none H le intro!: ASSERT_leI)
  show \<open>(M', M) \<in> trail_pol \<A> \<Longrightarrow> L \<in># \<A> \<Longrightarrow> defined_atm_pol_pre M' L\<close>
    using H le by (auto simp: defined_atm_pol_pre_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
qed


subparagraph \<open>Reasons\<close>

definition get_propagation_reason_pol :: \<open>trail_pol \<Rightarrow> nat literal \<Rightarrow> nat option nres\<close> where
  \<open>get_propagation_reason_pol = (\<lambda>(_, _, _, reasons, _) L. do {
      ASSERT(atm_of L < length reasons);
      let r = reasons ! atm_of L;
      RETURN (if r = DECISION_REASON then None else Some r)})\<close>

lemma get_propagation_reason_pol:
  \<open>(uncurry get_propagation_reason_pol, uncurry get_propagation_reason) \<in>
       [\<lambda>(M, L). L \<in> lits_of_l M]\<^sub>f trail_pol \<A> \<times>\<^sub>r Id \<rightarrow> \<langle>\<langle>nat_rel\<rangle>option_rel\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding lits_of_def
  apply clarify
  apply (rename_tac a aa ab ac b ba ad bb x, case_tac x)
  by (auto simp: get_propagation_reason_def get_propagation_reason_pol_def
      trail_pol_def ann_lits_split_reasons_def lits_of_def assert_bind_spec_conv)


definition get_propagation_reason_raw_pol :: \<open>trail_pol \<Rightarrow> nat literal \<Rightarrow> nat nres\<close> where
  \<open>get_propagation_reason_raw_pol = (\<lambda>(_, _, _, reasons, _) L. do {
      ASSERT(atm_of L < length reasons);
      let r = reasons ! atm_of L;
      RETURN r})\<close>

text \<open>The version \<^term>\<open>get_propagation_reason\<close> can return the reason, but does not have to: it can be
more suitable for specification (like for the conflict minimisation, where finding the reason is
not mandatory).

The following version \<^emph>\<open>always\<close> returns the reasons if there is one. Remark that both functions
are linked to the same code (but \<^term>\<open>get_propagation_reason\<close> can be called first with some additional
filtering later).
\<close>
definition (in -) get_the_propagation_reason
  :: \<open>('v, 'mark) ann_lits \<Rightarrow> 'v literal \<Rightarrow> 'mark option nres\<close>
where
  \<open>get_the_propagation_reason M L = SPEC(\<lambda>C.
     (C \<noteq> None \<longleftrightarrow> Propagated L (the C) \<in> set M) \<and>
     (C = None \<longleftrightarrow> Decided L \<in> set M \<or> L \<notin> lits_of_l M))\<close>

lemma no_dup_Decided_PropedD:
  \<open>no_dup ad \<Longrightarrow> Decided L \<in> set ad \<Longrightarrow> Propagated L C \<in> set ad \<Longrightarrow> False\<close>
  by (metis annotated_lit.distinct(1) in_set_conv_decomp lit_of.simps(1) lit_of.simps(2)
    no_dup_appendD no_dup_cons undefined_notin xy_in_set_cases)


definition get_the_propagation_reason_pol :: \<open>trail_pol \<Rightarrow> nat literal \<Rightarrow> nat option nres\<close> where
  \<open>get_the_propagation_reason_pol = (\<lambda>(_, xs, _, reasons, _) L. do {
      ASSERT(atm_of L < length reasons);
      ASSERT(nat_of_lit L < length xs);
      let r = reasons ! atm_of L;
      RETURN (if xs ! nat_of_lit L = SET_TRUE \<and> r \<noteq> DECISION_REASON then Some r else None)})\<close>

lemma get_the_propagation_reason_pol:
  \<open>(uncurry get_the_propagation_reason_pol, uncurry get_the_propagation_reason) \<in>
       [\<lambda>(M, L). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f trail_pol \<A> \<times>\<^sub>r Id \<rightarrow> \<langle>\<langle>nat_rel\<rangle>option_rel\<rangle> nres_rel\<close>
proof -
  have [dest]: \<open>no_dup bb \<Longrightarrow>
       SET_TRUE = polarity bb (Pos x1) \<Longrightarrow> Pos x1 \<in> lits_of_l bb \<and> Neg x1 \<notin> lits_of_l bb\<close> for bb x1
    by (auto simp: polarity_def split: if_splits dest: no_dup_consistentD)
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding lits_of_def get_the_propagation_reason_def uncurry_def get_the_propagation_reason_pol_def
    apply clarify
    apply (refine_vcg)
    subgoal
      by (auto simp: get_the_propagation_reason_def get_the_propagation_reason_pol_def Let_def
        trail_pol_def ann_lits_split_reasons_def assert_bind_spec_conv
        dest!: multi_member_split[of _ \<open>\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>])[]
    subgoal
      by (auto simp: get_the_propagation_reason_def get_the_propagation_reason_pol_def Let_def
        trail_pol_def ann_lits_split_reasons_def assert_bind_spec_conv
        dest!: multi_member_split[of _ \<open>\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>])[]
    subgoal for a aa ab ac ad b ba ae bb
      apply (cases \<open>aa ! nat_of_lit ba \<noteq> SET_TRUE\<close>)
      apply (subgoal_tac \<open>ba \<notin> lits_of_l ae\<close>)
      prefer 2
      subgoal
        by (auto simp: get_the_propagation_reason_def get_the_propagation_reason_pol_def Let_def
          trail_pol_def ann_lits_split_reasons_def assert_bind_spec_conv polarity_spec'(2)
          dest: multi_member_split[of _ \<open>\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>])[]
      subgoal
        by (auto simp: lits_of_def dest: imageI[of _ _ lit_of])

      apply (subgoal_tac \<open>ba \<in> lits_of_l ae\<close>)
      prefer 2
      subgoal
        by (auto simp: get_the_propagation_reason_def get_the_propagation_reason_pol_def Let_def
          trail_pol_def ann_lits_split_reasons_def assert_bind_spec_conv polarity_spec'(2)
          dest: multi_member_split[of _ \<open>\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>])[]
      subgoal
       apply (auto simp: get_the_propagation_reason_def get_the_propagation_reason_pol_def Let_def
        trail_pol_def ann_lits_split_reasons_def assert_bind_spec_conv lits_of_def
        dest!: multi_member_split[of _ \<open>\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>])[]
        apply (case_tac x; auto)
        apply (case_tac x; auto)
        done
      done
    done
qed


paragraph \<open>Direct access to elements in the trail\<close>

definition (in -) rev_trail_nth where
  \<open>rev_trail_nth M i = lit_of (rev M ! i)\<close>

definition (in -) isa_trail_nth :: \<open>trail_pol \<Rightarrow> nat \<Rightarrow> nat literal nres\<close> where
  \<open>isa_trail_nth = (\<lambda>(M, _) i. do {
    ASSERT(i < length M);
    RETURN (M ! i)
  })\<close>

lemma isa_trail_nth_rev_trail_nth:
  \<open>(uncurry isa_trail_nth, uncurry (RETURN oo rev_trail_nth)) \<in>
    [\<lambda>(M, i). i < length M]\<^sub>f trail_pol \<A> \<times>\<^sub>r nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: isa_trail_nth_def rev_trail_nth_def trail_pol_def ann_lits_split_reasons_def
    intro!: ASSERT_leI)


text \<open>We here define a variant of the trail representation, where the the control stack is out of
  sync of the trail (i.e., there are some leftovers at the end). This might make backtracking a
  little faster.
\<close>

definition trail_pol_no_CS :: \<open>nat multiset \<Rightarrow> (trail_pol \<times> (nat, nat) ann_lits) set\<close>
where
  \<open>trail_pol_no_CS \<A> =
   {((M', xs, lvls, reasons, k, cs), M). ((M', reasons), M) \<in> ann_lits_split_reasons \<A> \<and>
    no_dup M \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. nat_of_lit L < length xs \<and> xs ! (nat_of_lit L) = polarity M L) \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. atm_of L < length lvls \<and> lvls ! (atm_of L) = get_level M L) \<and>
    (\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<and>
    isasat_input_bounded \<A> \<and>
    control_stack (take (count_decided M) cs) M
  }\<close>

definition tl_trailt_tr_no_CS :: \<open>trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>tl_trailt_tr_no_CS = (\<lambda>(M', xs, lvls, reasons, k, cs).
    let L = last M' in
    (butlast M',
    let xs = xs[nat_of_lit L := None] in xs[nat_of_lit (-L) := None],
    lvls[atm_of L := 0],
    reasons, k, cs))\<close>

definition tl_trailt_tr_no_CS_pre where
  \<open>tl_trailt_tr_no_CS_pre = (\<lambda>(M, xs, lvls, reason, k, cs). M \<noteq> [] \<and> nat_of_lit(last M) < length xs \<and>
        nat_of_lit(-last M) < length xs  \<and> atm_of (last M) < length lvls \<and>
        atm_of (last M) < length reason)\<close>

lemma control_stack_take_Suc_count_dec_unstack:
 \<open>control_stack (take (Suc (count_decided M's)) cs) (Decided x1 # M's) \<Longrightarrow>
    control_stack (take (count_decided M's) cs) M's\<close>
  using control_stack_length_count_dec[of \<open>take (Suc (count_decided M's)) cs\<close> \<open>Decided x1 # M's\<close>]
  by (auto simp: min_def take_Suc_conv_app_nth split: if_splits elim: control_stackE)

lemma tl_trailt_tr_no_CS_pre:
  assumes \<open>(M', M) \<in> trail_pol_no_CS \<A>\<close> and \<open>M \<noteq> []\<close>
  shows \<open>tl_trailt_tr_no_CS_pre M'\<close>
proof -
  have [simp]: \<open>x \<noteq> [] \<Longrightarrow> is_decided (last x) \<Longrightarrow> Suc 0 \<le> count_decided x\<close> for x
    by (cases x rule: rev_cases) auto
  show ?thesis
    using assms
    unfolding trail_pol_def comp_def RETURN_refine_iff trail_pol_no_CS_def Let_def
      tl_trailt_tr_no_CS_def tl_trailt_tr_no_CS_pre_def
    by (cases M; cases \<open>hd M\<close>)
      (auto simp: trail_pol_no_CS_def ann_lits_split_reasons_def uminus_\<A>\<^sub>i\<^sub>n_iff
          rev_map[symmetric] hd_append hd_map simp del: rev_map
        intro!: ext)
qed

lemma tl_trail_tr_no_CS:
  \<open>((RETURN o tl_trailt_tr_no_CS), (RETURN o tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>f trail_pol_no_CS \<A> \<rightarrow> \<langle>trail_pol_no_CS \<A>\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI, rename_tac x y, case_tac \<open>y\<close>)
  subgoal by fast
  subgoal for M M' L M's
    unfolding trail_pol_def comp_def RETURN_refine_iff trail_pol_no_CS_def Let_def
      tl_trailt_tr_no_CS_def
    apply clarify
    apply (intro conjI; clarify?; (intro conjI)?)
    subgoal
      by (auto simp: trail_pol_def polarity_atm_def tl_trailt_tr_def
	  ann_lits_split_reasons_def Let_def)
    subgoal by (auto simp: trail_pol_def polarity_atm_def tl_trailt_tr_def)
    subgoal by (auto simp: polarity_atm_def tl_trailt_tr_def Let_def)
    subgoal
      by (cases \<open>lit_of L\<close>)
	(auto simp: polarity_def tl_trailt_tr_def Decided_Propagated_in_iff_in_lits_of_l
	  uminus_lit_swap Let_def
	  dest: ann_lits_split_reasons_map_lit_of)
    subgoal
      by (auto simp: polarity_atm_def tl_trailt_tr_def Let_def
	 atm_of_eq_atm_of get_level_cons_if)
    subgoal
      by (auto simp: polarity_atm_def tl_trailt_tr_def
	 atm_of_eq_atm_of get_level_cons_if Let_def
	  dest!: ann_lits_split_reasons_map_lit_of)
    subgoal
      by (cases \<open>L\<close>)
	(auto simp: tl_trailt_tr_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff ann_lits_split_reasons_def
	  control_stack_dec_butlast
	  dest: no_dup_consistentD)
    subgoal
      by (cases \<open>L\<close>)
	(auto simp: tl_trailt_tr_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff ann_lits_split_reasons_def
	  control_stack_dec_butlast control_stack_take_Suc_count_dec_unstack
	  dest: no_dup_consistentD ann_lits_split_reasons_map_lit_of)
    done
  done

definition trail_conv_to_no_CS :: \<open>(nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>trail_conv_to_no_CS M = M\<close>

definition trail_pol_conv_to_no_CS :: \<open>trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>trail_pol_conv_to_no_CS M = M\<close>

lemma id_trail_conv_to_no_CS:
  \<open>(RETURN o trail_pol_conv_to_no_CS, RETURN o trail_conv_to_no_CS) \<in> trail_pol \<A> \<rightarrow>\<^sub>f \<langle>trail_pol_no_CS \<A>\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: trail_pol_no_CS_def trail_conv_to_no_CS_def trail_pol_def
      control_stack_length_count_dec trail_pol_conv_to_no_CS_def
      intro: ext)

definition trail_conv_back :: \<open>nat \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>trail_conv_back j M = M\<close>

definition (in -) trail_conv_back_imp :: \<open>nat \<Rightarrow> trail_pol \<Rightarrow> trail_pol nres\<close> where
  \<open>trail_conv_back_imp j = (\<lambda>(M, xs, lvls, reason, _, cs). do {
     ASSERT(j \<le> length cs); RETURN (M, xs, lvls, reason, j, take (j) cs)})\<close>

lemma trail_conv_back:
  \<open>(uncurry trail_conv_back_imp, uncurry (RETURN oo trail_conv_back))
      \<in> [\<lambda>(k, M). k = count_decided M]\<^sub>f nat_rel \<times>\<^sub>f trail_pol_no_CS \<A> \<rightarrow> \<langle>trail_pol \<A>\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (force simp: trail_pol_no_CS_def trail_conv_to_no_CS_def trail_pol_def
      control_stack_length_count_dec trail_conv_back_def trail_conv_back_imp_def
      intro: ext intro!: ASSERT_refine_left
      dest: control_stack_length_count_dec multi_member_split)

definition (in -)take_arl where
  \<open>take_arl = (\<lambda>i (xs, j). (xs, i))\<close>


lemma isa_trail_nth_rev_trail_nth_no_CS:
  \<open>(uncurry isa_trail_nth, uncurry (RETURN oo rev_trail_nth)) \<in>
    [\<lambda>(M, i). i < length M]\<^sub>f trail_pol_no_CS \<A> \<times>\<^sub>r nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: isa_trail_nth_def rev_trail_nth_def trail_pol_def ann_lits_split_reasons_def
      trail_pol_no_CS_def
    intro!: ASSERT_leI)

lemma trail_pol_no_CS_alt_def:
  \<open>trail_pol_no_CS \<A> =
    {((M', xs, lvls, reasons, k, cs), M). ((M', reasons), M) \<in> ann_lits_split_reasons \<A> \<and>
    no_dup M \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. nat_of_lit L < length xs \<and> xs ! (nat_of_lit L) = polarity M L) \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. atm_of L < length lvls \<and> lvls ! (atm_of L) = get_level M L) \<and>
    (\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<and>
    control_stack (take (count_decided M) cs) M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M \<and>
    length M < uint32_max \<and>
    length M \<le> uint32_max div 2 + 1 \<and>
    count_decided M < uint32_max \<and>
    length M' = length M \<and>
    isasat_input_bounded \<A> \<and>
    M' = map lit_of (rev M)
   }\<close>
proof -
  have [intro!]: \<open>length M < n \<Longrightarrow> count_decided M < n\<close> for M n
    using length_filter_le[of is_decided M]
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def uint32_max_def count_decided_def
        simp del: length_filter_le
        dest: length_trail_uint32_max_div2)
  show ?thesis
    unfolding trail_pol_no_CS_def
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def uint32_max_def ann_lits_split_reasons_def
        dest: length_trail_uint32_max_div2
	simp del: isasat_input_bounded_def)
qed


(* TODO: Kill the other definition *)
lemma isa_length_trail_length_u_no_CS:
  \<open>(RETURN o isa_length_trail, RETURN o length_uint32_nat) \<in> trail_pol_no_CS \<A> \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: isa_length_trail_def trail_pol_no_CS_alt_def ann_lits_split_reasons_def
      intro!: ASSERT_leI)


lemma control_stack_is_decided:
  \<open>control_stack cs M \<Longrightarrow> c\<in>set cs \<Longrightarrow> is_decided ((rev M)!c)\<close>
  by (induction arbitrary: c rule: control_stack.induct) (auto simp: nth_append
      dest: control_stack_le_length_M)

lemma control_stack_distinct:
  \<open>control_stack cs M \<Longrightarrow> distinct cs\<close>
  by (induction rule: control_stack.induct) (auto simp: nth_append
      dest: control_stack_le_length_M)

lemma control_stack_level_control_stack:
  assumes
    cs: \<open>control_stack cs M\<close> and
    n_d: \<open>no_dup M\<close> and
    i: \<open>i < length cs\<close>
  shows \<open>get_level M (lit_of (rev M ! (cs ! i))) = Suc i\<close>
proof -
  define L where \<open>L = rev M ! (cs ! i)\<close>
  have csi: \<open>cs ! i < length M\<close>
    using cs i by (auto intro: control_stack_le_length_M)
  then have L_M: \<open>L \<in> set M\<close>
    using nth_mem[of \<open>cs !i\<close> \<open>rev M\<close>] unfolding L_def by (auto simp del: nth_mem)
  have dec_L: \<open>is_decided L\<close>
    using control_stack_is_decided[OF cs] i unfolding L_def by auto
  then have \<open>rev M!(cs ! (get_level M (lit_of L) - 1)) = L\<close>
    using control_stack_rev_get_lev[OF cs n_d L_M] by auto
  moreover have \<open>distinct M\<close>
    using no_dup_distinct[OF n_d] unfolding mset_map[symmetric] distinct_mset_mset_distinct
    by (rule distinct_mapI)

  moreover have lev0:  \<open>get_level M (lit_of L) \<ge> 1\<close>
    using split_list[OF L_M] n_d dec_L by (auto simp: get_level_append_if)
  moreover have \<open>cs ! (get_level M (lit_of (rev M ! (cs ! i))) - Suc 0) < length M\<close>
    using control_stack_le_length_M[OF cs,
         of \<open>cs ! (get_level M (lit_of (rev M ! (cs ! i))) - Suc 0)\<close>, OF nth_mem]
      control_stack_length_count_dec[OF cs] count_decided_ge_get_level[of M
          \<open>lit_of (rev M ! (cs ! i))\<close>] lev0
    by (auto simp: L_def)
  ultimately have \<open>cs ! (get_level M (lit_of L) - 1) = cs ! i\<close>
    using nth_eq_iff_index_eq[of \<open>rev M\<close>] csi unfolding L_def by auto
  then have \<open>i = get_level M (lit_of L) - 1\<close>
    using nth_eq_iff_index_eq[OF control_stack_distinct[OF cs], of i \<open>get_level M (lit_of L) - 1\<close>]
      i lev0 count_decided_ge_get_level[of M \<open>lit_of (rev M ! (cs ! i))\<close>]
    control_stack_length_count_dec[OF cs]
    by (auto simp: L_def)
  then show ?thesis using lev0 unfolding L_def[symmetric] by auto
qed


definition get_pos_of_level_in_trail where
  \<open>get_pos_of_level_in_trail M\<^sub>0 lev =
     SPEC(\<lambda>i. i < length M\<^sub>0 \<and> is_decided (rev M\<^sub>0!i) \<and> get_level M\<^sub>0 (lit_of (rev M\<^sub>0!i)) = lev+1)\<close>

definition (in -) get_pos_of_level_in_trail_imp where
  \<open>get_pos_of_level_in_trail_imp = (\<lambda>(M', xs, lvls, reasons, k, cs) lev. do {
      ASSERT(lev < length cs);
      RETURN (cs ! lev)
   })\<close>
definition get_pos_of_level_in_trail_pre where
  \<open>get_pos_of_level_in_trail_pre = (\<lambda>(M, lev). lev < count_decided M)\<close>

lemma get_pos_of_level_in_trail_imp_get_pos_of_level_in_trail:
   \<open>(uncurry get_pos_of_level_in_trail_imp, uncurry get_pos_of_level_in_trail) \<in>
    [get_pos_of_level_in_trail_pre]\<^sub>f trail_pol_no_CS \<A> \<times>\<^sub>f nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  apply (intro nres_relI frefI)
  unfolding get_pos_of_level_in_trail_imp_def uncurry_def get_pos_of_level_in_trail_def
    get_pos_of_level_in_trail_pre_def
  apply clarify
  apply (rule ASSERT_leI)
  subgoal
    by (auto simp: trail_pol_no_CS_alt_def dest!: control_stack_length_count_dec)
  subgoal for a aa ab ac ad b ba ae bb
    by (auto simp: trail_pol_no_CS_def control_stack_length_count_dec in_set_take_conv_nth
        intro!: control_stack_le_length_M control_stack_is_decided
        dest: control_stack_level_control_stack)
  done

lemma get_pos_of_level_in_trail_imp_get_pos_of_level_in_trail_CS:
   \<open>(uncurry get_pos_of_level_in_trail_imp, uncurry get_pos_of_level_in_trail) \<in>
    [get_pos_of_level_in_trail_pre]\<^sub>f trail_pol \<A> \<times>\<^sub>f nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  apply (intro nres_relI frefI)
  unfolding get_pos_of_level_in_trail_imp_def uncurry_def get_pos_of_level_in_trail_def
    get_pos_of_level_in_trail_pre_def
  apply clarify
  apply (rule ASSERT_leI)
  subgoal
    by (auto simp: trail_pol_def dest!: control_stack_length_count_dec)
  subgoal for a aa ab ac ad b ba ae bb
    by (auto simp: trail_pol_def control_stack_length_count_dec in_set_take_conv_nth
        intro!: control_stack_le_length_M control_stack_is_decided
        dest: control_stack_level_control_stack)
  done

lemma lit_of_last_trail_pol_lit_of_last_trail_no_CS:
   \<open>(RETURN o lit_of_last_trail_pol, RETURN o lit_of_hd_trail) \<in>
         [\<lambda>S. S \<noteq> []]\<^sub>f trail_pol_no_CS \<A> \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (auto simp: lit_of_hd_trail_def trail_pol_no_CS_def lit_of_last_trail_pol_def
     ann_lits_split_reasons_def hd_map rev_map[symmetric] last_rev
      intro!: frefI nres_relI)

end
