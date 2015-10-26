theory DPLL_Implementation
imports Propo_DPLL "~~/src/HOL/Library/Code_Target_Numeral"
begin

section \<open>Simple Implementation of DPLL\<close>

subsection \<open>Decide\<close>
fun find_first_unused_var :: "int literal list list \<Rightarrow> int literal set \<Rightarrow> int literal option"  where
"find_first_unused_var (a # l) M =
  (case List.find (\<lambda>lit. lit \<notin> M \<and> -lit \<notin> M) a of
    None \<Rightarrow> find_first_unused_var l M
  | Some a \<Rightarrow> Some a)" |
"find_first_unused_var [] _ = None"

lemma find_none[iff]:
  "List.find (\<lambda>lit. lit \<notin> M \<and> -lit \<notin> M) a = None \<longleftrightarrow>  atm_of ` set a \<subseteq> atm_of `  M"
  apply (induct a)
  using atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
    by (force simp add:  atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)+

lemma find_some: "List.find (\<lambda>lit. lit \<notin> M \<and> -lit \<notin> M) a = Some b \<Longrightarrow> b \<in> set a \<and> b \<notin> M \<and> -b \<notin> M"
  by (metis find_Some_iff nth_mem)

lemma find_first_unused_var_None[iff]:
  "find_first_unused_var l M = None \<longleftrightarrow> (\<forall>a \<in> set l. atm_of ` set a \<subseteq> atm_of `  M)"
  apply(induct l, auto split: option.split)
  using find_some[of M] by (smt atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set image_subset_iff)+

lemma find_first_unused_var_Some:
  "find_first_unused_var l M = Some a \<Longrightarrow> (\<exists>m \<in> set l. a \<in> set m \<and> a \<notin> M \<and> -a \<notin> M)"
  apply(induct l, auto split: option.split)
  using find_some[of M] by (metis (lifting) option.case_eq_if option.collapse)+

lemma find_first_unused_var_undefined:
  "find_first_unused_var l (lits_of Ms) = Some a \<Longrightarrow> undefined_lit a Ms"
  using find_first_unused_var_Some[of l "lits_of Ms" a] Marked_Propagated_in_iff_in_lits_of by blast


value "backtrack_split [Marked (Pos (Suc 0)) Level]"
value "\<exists>C \<in> set [[Pos (Suc 0), Neg (Suc 0)]].
  (\<forall>c \<in> set C. -c \<in> lits_of [Marked (Pos (Suc 0)) Level])"

subsection \<open>Propagate\<close>
subsubsection \<open>Detecting unit propagation\<close>
text \<open>The following theorem holds:\<close>
lemma lits_of_unfold[iff]:
  "(\<forall>c \<in> set C. -c \<in> lits_of Ms) \<longleftrightarrow> Ms \<Turnstile>as CNot (mset C)"
  unfolding true_annots_def Ball_def true_annot_def CNot_def mem_set_multiset_eq by auto
text \<open>The right-hand version is written at a high-level, but only the left-hand side is executable.\<close>

text \<open>detecting if a clause is a clause where a single variable remains to decide.\<close>
definition is_unit_clause :: "'a literal list \<Rightarrow> ('a, 'b, 'c) marked_lit list \<Rightarrow> 'a literal option"
  where
 "is_unit_clause l M =
   (case List.filter (\<lambda>a. atm_of a \<notin> atm_of ` lits_of M) l of
     [] \<Rightarrow> None
   | a # [] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None
   | _ \<Rightarrow> None)"

text \<open>Here is the code equivalent:\<close>
definition is_unit_clause_code ::
  "'a literal list \<Rightarrow> ('a, 'b, 'c) marked_lit list \<Rightarrow> 'a literal option" where
 "is_unit_clause_code l M =
   (case List.filter (\<lambda>a. atm_of a \<notin> atm_of ` lits_of M) l of
     [] \<Rightarrow> None
   | a # [] \<Rightarrow> if (\<forall>c \<in>set (remove1 a l). -c \<in> lits_of M) then Some a else None
   | _ \<Rightarrow> None)"

lemma [code]:
  "is_unit_clause l M = is_unit_clause_code l M"
proof -
  have 1: "\<And>a. (\<forall>c\<in>set (remove1 a l). - c \<in> lits_of M) \<longleftrightarrow> M \<Turnstile>as CNot (mset l - {#a#})"
    using lits_of_unfold[of "remove1 _ l", of _ M] by simp
  show ?thesis
    unfolding is_unit_clause_code_def is_unit_clause_def 1 by blast
qed

lemma is_unit_clause_some_undef: "is_unit_clause l M = Some a \<Longrightarrow> undefined_lit a M"
  unfolding is_unit_clause_def lits_of_def
proof -
  assume "(case [a\<leftarrow>l . atm_of a \<notin> atm_of ` lit_of ` set M] of [] \<Rightarrow> None
        | [a] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None
        | a # ab # xa \<Rightarrow> Map.empty xa) = Some a"
  hence "a \<in> set [a\<leftarrow>l . atm_of a \<notin> atm_of ` lit_of ` set M]"
    apply (case_tac "[a\<leftarrow>l . atm_of a \<notin> atm_of ` lit_of ` set M]", auto)
    apply (case_tac list, auto)
    apply (case_tac "M \<Turnstile>as CNot (mset l - {#aa#})")
    by auto
  hence "atm_of a \<notin> atm_of ` lit_of ` set M" by auto
  thus ?thesis
    by (simp add: Marked_Propagated_in_iff_in_lits_of
      atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set lits_of_def)
qed

lemma is_unit_clause_some_CNot: "is_unit_clause l M = Some a \<Longrightarrow> M \<Turnstile>as CNot (mset l - {#a#})"
  unfolding is_unit_clause_def lits_of_def
proof -
  assume "(case [a\<leftarrow>l . atm_of a \<notin> atm_of ` lit_of ` set M] of [] \<Rightarrow> None
          | [a] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None
          | a # ab # xa \<Rightarrow> Map.empty xa) = Some a"
  thus ?thesis
    apply (case_tac "[a\<leftarrow>l . atm_of a \<notin> atm_of ` lit_of ` set M]", auto)
    apply (case_tac list, auto)
    apply (case_tac "M \<Turnstile>as CNot (mset l - {#aa#})")
    by auto
qed

lemma is_unit_clause_some_in: "is_unit_clause l M = Some a \<Longrightarrow> a \<in> set l"
  unfolding is_unit_clause_def lits_of_def
proof -
  assume "(case [a\<leftarrow>l . atm_of a \<notin> atm_of ` lit_of ` set M] of [] \<Rightarrow> None
          | [a] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None
          | a # ab # xa \<Rightarrow> Map.empty xa) = Some a"
  thus "a \<in> set l"
    apply (case_tac "[a\<leftarrow>l . atm_of a \<notin> atm_of ` lit_of ` set M]", auto)
    apply (case_tac list, auto)
    apply (case_tac "M \<Turnstile>as CNot (mset l - {#aa#})")
    apply auto
    by (metis (no_types, lifting) insertI1 list.simps(15) mem_Collect_eq set_filter)
qed

lemma is_unit_clause_empty[simp]: "is_unit_clause [] M = None"
  unfolding is_unit_clause_def by auto

subsubsection \<open>Unit propagation for all clauses\<close>
text \<open>Finding the first clause to propagate\<close>
fun find_first_unit_clause
  :: "'a literal list list \<Rightarrow> ('a, 'b, 'c) marked_lit list \<Rightarrow> 'a literal option"  where
"find_first_unit_clause (a # l) M =
  (case is_unit_clause a M of
    None \<Rightarrow> find_first_unit_clause l M
  | Some a \<Rightarrow> Some a)" |
"find_first_unit_clause [] _ = None"

lemma find_first_unit_clause_some:
  assumes "find_first_unit_clause l M = Some a"
  shows "\<exists>c \<in> set l. M \<Turnstile>as CNot (mset c - {#a#}) \<and> undefined_lit a M \<and> a \<in> set c"
  using assms
  apply (induct l)
   apply simp
  by (case_tac "is_unit_clause aa M")
     (auto dest: is_unit_clause_some_CNot is_unit_clause_some_undef is_unit_clause_some_in)

subsection \<open>Combining the two steps: a DPLL step\<close>
definition DPLL_step :: "int dpll_annoted_lits \<times> int literal list list
  \<Rightarrow> int dpll_annoted_lits \<times> int literal list list"  where
"DPLL_step = (\<lambda>(Ms, N).
  (case find_first_unit_clause N Ms of
    Some L \<Rightarrow> (Propagated L Proped # Ms, N)
  | _ \<Rightarrow>
    if \<exists>C \<in> set N. (\<forall>c \<in> set C. -c \<in> lits_of Ms)
    then
      (case backtrack_split Ms of
        (_, L # M) \<Rightarrow>  (Propagated (- (lit_of L)) Proped # M, N)
      | (_, _) \<Rightarrow> (Ms, N)
      )
    else
    (case find_first_unused_var N (lits_of Ms) of
        Some a \<Rightarrow> (Marked a Level # Ms, N)
      | None \<Rightarrow> (Ms, N))))"

text \<open>Example of propagation:\<close>
value "DPLL_step ([Marked (Neg 1) Level], [[Pos (1::int), Neg 2]])"

text \<open>We define the conversion function between the states as defined in \<open>Propo_DPLL\<close> (with
  multisets) and here (with lists).\<close>
abbreviation "toS \<equiv> \<lambda>(Ms::(int, dpll_marked_level, dpll_mark) marked_lit list)
                      (N:: int literal list list). (Ms, set (map mset N)) "
abbreviation "toS' \<equiv> \<lambda>(Ms::(int, dpll_marked_level, dpll_mark) marked_lit list,
                          N:: int literal list list). (Ms, set (map mset N)) "

text \<open>Proof of correctness of @{term DPLL_step}\<close>
lemma DPLL_step_is_a_dpll_step:
  assumes step: "(Ms', N') = DPLL_step (Ms, N)"
  and neq: "(Ms, N) \<noteq> (Ms', N')"
  shows "dpll (toS Ms N) (toS Ms' N')"
proof -
  let ?S = "(Ms, set (map mset N))"
  { fix L
    assume unit: "find_first_unit_clause N Ms = Some L"
    hence Ms'N: "(Ms', N') = (Propagated L Proped # Ms, N)" using step unfolding DPLL_step_def by auto
    obtain C where
      C: "C \<in> set N" and
      Ms: "Ms \<Turnstile>as CNot (mset C - {#L#})" and
      undef: "undefined_lit L Ms" and
      "L \<in> set C" using find_first_unit_clause_some[OF unit] by metis
    have "dpll (Ms, set (map mset N))
         (Propagated L Proped # fst (Ms, set (map mset N)), snd (Ms, set (map mset N)))"
      apply (rule dpll.propagate[of "mset C - {#L#}" L ?S])
      using Ms undef C `L \<in> set C` unfolding mem_set_multiset_eq by (auto simp add: C)
    hence ?thesis using Ms'N by auto
  }
  moreover
  { assume unit: "find_first_unit_clause N Ms = None"
    assume exC: "\<exists>C \<in> set N. Ms \<Turnstile>as CNot (mset C)"
    then obtain C where C: "C \<in> set N" and Ms: "Ms \<Turnstile>as CNot (mset C)" by auto
    then obtain L M M' where bt: "backtrack_split Ms  = (M', L # M)"
      using step exC neq unfolding DPLL_step_def prod.case unit
      by (cases "backtrack_split Ms", case_tac b) auto
    hence "is_marked L" using backtrack_split_snd_hd_marked[of Ms] by auto
    have 1: "dpll (Ms, set (map mset N))
                  (Propagated (- lit_of L) Proped # M, snd (Ms, set (map mset N)))"
      apply (rule dpll.backtrack[OF _ `is_marked L`, of ])
      using C Ms bt by auto
    moreover have "(Ms', N') = (Propagated (- (lit_of L)) Proped # M, N)"
      using step exC unfolding DPLL_step_def bt prod.case unit by auto
    ultimately have ?thesis by auto
  }
  moreover
  { assume unit: "find_first_unit_clause N Ms = None"
    assume exC: "\<not> (\<exists>C \<in> set N. Ms \<Turnstile>as CNot (mset C))"
    obtain L where unused: "find_first_unused_var N (lits_of Ms) = Some L"
      using step exC neq unfolding DPLL_step_def prod.case unit
      by (cases "find_first_unused_var N (lits_of Ms)") auto
    have "dpll (Ms, set (map mset N))
               (Marked L Level # fst (Ms, set (map mset N)), snd (Ms, set (map mset N)))"
    apply (rule dpll.decided[of L ?S])
    using find_first_unused_var_Some[OF unused]
    by (auto simp add: Marked_Propagated_in_iff_in_lits_of atms_of_m_def)
   moreover have "(Ms', N') = (Marked L Level # Ms, N)"
     using step exC unfolding DPLL_step_def unused prod.case unit by auto
    ultimately have ?thesis by auto
  }
  ultimately show ?thesis by blast
qed

lemma DPLL_step_stuck_final_state:
  assumes step: "(Ms, N) = DPLL_step (Ms, N)"
  shows "final_dpll_state (toS Ms N)"
proof -
  have unit: "find_first_unit_clause N Ms = None" using step unfolding DPLL_step_def by (auto split:option.splits)

  { assume n: "\<exists>C \<in> set N. Ms \<Turnstile>as CNot (mset C)"
    hence Ms: "(Ms, N) = (case backtrack_split Ms of (x, []) \<Rightarrow> (Ms, N) | (x, L # M) \<Rightarrow> (Propagated (- lit_of L) Proped # M, N))"
      using step unfolding DPLL_step_def by (simp add:unit)

  have "snd (backtrack_split Ms) = []"
    proof (cases "backtrack_split Ms", cases "snd (backtrack_split Ms)")
      fix a b
      assume "backtrack_split Ms = (a, b)" and "snd (backtrack_split Ms) = []"
      thus "snd (backtrack_split Ms) = []" by blast
    next
      fix a b aa list
      assume
        bt: "backtrack_split Ms = (a, b)" and
        bt': "snd (backtrack_split Ms) = aa # list"
      hence Ms: "Ms = Propagated (- lit_of aa) Proped # list" using Ms by auto
      have "is_marked aa" using backtrack_split_snd_hd_marked[of Ms] bt bt' by auto
      moreover have "fst (backtrack_split Ms) @ aa # list = Ms"
        using backtrack_split_list_eq[of Ms] bt' by auto
      ultimately have False unfolding Ms by auto
      thus "snd (backtrack_split Ms) = []" by blast
    qed

    hence ?thesis
      using n backtrack_snd_empty_not_marked[of Ms] unfolding final_dpll_state_def
      by (cases "backtrack_split Ms") auto
  }
  moreover {
    assume n: "\<not> (\<exists>C \<in> set N. Ms \<Turnstile>as CNot (mset C))"
    hence "find_first_unused_var N (lits_of Ms) = None"
      using step unfolding DPLL_step_def by (simp add: unit split: option.splits)
    hence a: "\<forall>a \<in> set N. atm_of ` set a \<subseteq> atm_of `  (lits_of Ms)" by auto
    have "fst (toS Ms N) \<Turnstile>as snd (toS Ms N)" unfolding true_annots_def CNot_def Ball_def
      proof (clarify)
        fix x
        assume x: "x \<in> snd (toS Ms N)"
        hence "\<not>Ms \<Turnstile>as CNot  x" using n unfolding true_annots_def CNot_def Ball_def by auto
        moreover have "total_over_m (lits_of Ms) {x}"
          using a x image_iff in_mono atms_of_s_def
          unfolding total_over_m_def total_over_set_def lits_of_def by fastforce
        ultimately show "fst (toS Ms N) \<Turnstile>a x"
          using total_not_CNot[of "lits_of Ms" x] by (simp add: true_annot_def true_annots_true_cls)
      qed
    hence ?thesis unfolding final_dpll_state_def by blast
  }
  ultimately show ?thesis by blast
qed

subsection \<open>Adding invariants\<close>
subsubsection \<open>Invariant tested in the function\<close>
function DPLL_ci :: "int dpll_annoted_lits \<Rightarrow> int literal list list
  \<Rightarrow> int dpll_annoted_lits \<times> int literal list list" where
"DPLL_ci Ms N =
  (if \<not>dpll_all_inv (Ms, set (map mset N))
  then (Ms, N)
  else
   let (Ms', N') = DPLL_step (Ms, N) in
   if (Ms', N') = (Ms, N) then (Ms, N) else DPLL_ci Ms' N)"
  by fast+
termination
proof (relation "{(S', S).  (toS' S', toS' S) \<in> {(S', S). dpll_all_inv S \<and> dpll S S'}}")
  show  "wf {(S', S).(toS' S', toS' S) \<in> {(S', S). dpll_all_inv S \<and> dpll S S'}}"
    apply auto
    using  wf_if_measure_f[OF dpll_wf, of "toS'"] by auto
next
  fix Ms :: "int dpll_annoted_lits" and N x xa y
  assume"\<not> \<not> dpll_all_inv (toS Ms N)"
  and step: "x = DPLL_step (Ms, N)"
  and x: "(xa, y) = x"
  and "(xa, y) \<noteq> (Ms, N)"
  thus "((xa, N), Ms, N) \<in> {(S', S). (toS' S', toS' S) \<in> {(S', S). dpll_all_inv S \<and> dpll S S'}}"
    using DPLL_step_is_a_dpll_step dpll_same_clauses split_conv by fastforce
qed

subsubsection \<open>No invariant tested\<close>
function (domintros) DPLL_part:: "int dpll_annoted_lits \<Rightarrow> int literal list list \<Rightarrow> int dpll_annoted_lits \<times> int literal list list" where
"DPLL_part Ms N =
  (let (Ms', N') = DPLL_step (Ms, N) in
   if (Ms', N') = (Ms, N) then (Ms, N) else DPLL_part Ms' N)"
  by fast+

lemma snd_DPLL_step[simp]:
  "snd (DPLL_step (Ms, N)) = N"
  unfolding DPLL_step_def apply (auto split: split_if option.splits)
  by (case_tac "backtrack_split Ms", case_tac b, auto)+

lemma dpll_all_inv_implieS_2_eq3_and_dom:
  assumes "dpll_all_inv (Ms, set (map mset N))"
  shows "DPLL_ci Ms N = DPLL_part Ms N \<and> DPLL_part_dom (Ms, N)"
  using assms
proof (induct rule: DPLL_ci.induct)
  case (1 Ms N)
  have "snd (DPLL_step (Ms, N)) = N"  by auto
  then obtain Ms' where Ms': "DPLL_step (Ms, N) = (Ms', N)" by (case_tac "DPLL_step (Ms, N)") auto
  have inv': "dpll_all_inv (toS Ms' N)" by (metis (mono_tags) "1.prems" DPLL_step_is_a_dpll_step Ms'
    dpll_all_inv old.prod.inject)
  { assume "(Ms', N) \<noteq> (Ms, N)"
    hence "DPLL_ci Ms' N = DPLL_part Ms' N \<and> DPLL_part_dom (Ms', N)" using 1(1)[of _ Ms' N] Ms'
      1(2) inv' by auto
    hence "DPLL_part_dom (Ms, N)" using DPLL_part.domintros Ms' by fastforce
    moreover have "DPLL_ci Ms N = DPLL_part Ms N" using "1.prems" DPLL_part.psimps Ms'
      `DPLL_ci Ms' N = DPLL_part Ms' N \<and> DPLL_part_dom (Ms', N)` `DPLL_part_dom (Ms, N)` by auto
    ultimately have ?case by blast
  }
  moreover {
    assume "(Ms', N) = (Ms, N)"
    hence ?case using DPLL_part.domintros DPLL_part.psimps Ms' by fastforce
  }
  ultimately show ?case by blast
qed

lemma DPLL_ci_dpll_rtranclp:
  assumes "DPLL_ci Ms N = (Ms', N')"
  shows "dpll\<^sup>*\<^sup>* (toS Ms N) (toS Ms' N)"
  using assms
proof (induct Ms N arbitrary: Ms' N' rule: DPLL_ci.induct)
  case (1 Ms N Ms' N') note IH = this(1) and step = this(2)
  obtain S\<^sub>1 S\<^sub>2 where S: "(S\<^sub>1, S\<^sub>2) = DPLL_step (Ms, N)" by (case_tac "DPLL_step (Ms, N)") auto

  { assume "\<not>dpll_all_inv (toS Ms N)"
    hence "(Ms, N) = (Ms', N)" using step by auto
    hence ?case by auto
  }
  moreover
  { assume "dpll_all_inv (toS Ms N)"
    and "(S\<^sub>1, S\<^sub>2) = (Ms, N)"
    hence ?case using S step by auto
  }
  moreover
  { assume "dpll_all_inv (toS Ms N)"
    and "(S\<^sub>1, S\<^sub>2) \<noteq> (Ms, N)"
    moreover obtain S\<^sub>1' S\<^sub>2' where "DPLL_ci S\<^sub>1 N = (S\<^sub>1', S\<^sub>2')" by (case_tac "DPLL_ci S\<^sub>1 N") auto
    moreover have "DPLL_ci Ms N = DPLL_ci S\<^sub>1 N" using DPLL_ci.simps[of Ms N] calculation
      proof -
        have "(case (S\<^sub>1, S\<^sub>2) of (ms, lss) \<Rightarrow>
          if (ms, lss) = (Ms, N) then (Ms, N) else DPLL_ci ms N) = DPLL_ci Ms N"
          using S DPLL_ci.simps[of Ms N] calculation by presburger
        hence "(if (S\<^sub>1, S\<^sub>2) = (Ms, N) then (Ms, N) else DPLL_ci S\<^sub>1 N) = DPLL_ci Ms N"
          by fastforce
        thus ?thesis
          using calculation(2) by presburger (* 2 ms *)
      qed
    ultimately have "dpll\<^sup>*\<^sup>* (toS S\<^sub>1' N) (toS Ms' N)" using IH[of "(S\<^sub>1, S\<^sub>2)" S\<^sub>1 S\<^sub>2] S step by simp

    moreover have "dpll (toS Ms N) (toS S\<^sub>1 N)"
      by (metis DPLL_step_is_a_dpll_step S `(S\<^sub>1, S\<^sub>2) \<noteq> (Ms, N)` prod.sel(2) snd_DPLL_step)
    ultimately have ?case by (metis (mono_tags, hide_lams) IH S `(S\<^sub>1, S\<^sub>2) \<noteq> (Ms, N)`
      `DPLL_ci Ms N = DPLL_ci S\<^sub>1 N` `dpll_all_inv (toS Ms N)` converse_rtranclp_into_rtranclp
      local.step)
  }
  ultimately show ?case by blast
qed

lemma dpll_all_inv_dpll_tranclp_irrefl:
  assumes "dpll_all_inv (Ms, N)"
  and "dpll\<^sup>+\<^sup>+ (Ms, N) (Ms, N)"
  shows "False"
proof -
  have 1: "wf {(S', S). dpll_all_inv S \<and> dpll\<^sup>+\<^sup>+ S S'}" using dpll_wf_tranclp by auto
  have "((Ms, N), (Ms, N)) \<in> {(S', S). dpll_all_inv S \<and> dpll\<^sup>+\<^sup>+ S S'}" using assms by auto
  thus False using wf_not_refl[OF 1] by blast
qed

lemma DPLL_ci_final_state:
  assumes step: "DPLL_ci Ms N = (Ms, N)"
  and inv: "dpll_all_inv (toS Ms N)"
  shows "final_dpll_state (toS Ms N)"
proof  -
  have st: "dpll\<^sup>*\<^sup>* (toS Ms N) (toS Ms N)" using DPLL_ci_dpll_rtranclp[OF step] .
  have "DPLL_step (Ms, N) = (Ms, N)"
    proof (rule ccontr)
      obtain Ms' N' where Ms'N: "(Ms', N') = DPLL_step (Ms, N)"
        by (case_tac "DPLL_step (Ms, N)") auto
      assume "\<not> ?thesis"
      hence "DPLL_ci Ms' N = (Ms, N)" using step inv st Ms'N[symmetric] by fastforce
      hence "dpll\<^sup>+\<^sup>+ (toS Ms N) (toS Ms N)"
        by (metis DPLL_ci_dpll_rtranclp DPLL_step_is_a_dpll_step Ms'N `DPLL_step (Ms, N) \<noteq> (Ms, N)`
          prod.sel(2) rtranclp_into_tranclp2 snd_DPLL_step)
      thus False using dpll_all_inv_dpll_tranclp_irrefl inv by auto
    qed
  thus ?thesis using DPLL_step_stuck_final_state[of Ms N] by simp
qed

lemma DPLL_step_obtains:
  obtains Ms' where "(Ms', N) = DPLL_step (Ms, N)"
  unfolding DPLL_step_def apply (auto split: option.split)
  by (metis (no_types, hide_lams) eq_snd_iff snd_DPLL_step that)


lemma DPLL_ci_obtains:
  obtains Ms' where "(Ms', N) = DPLL_ci Ms N"
proof (induct rule: DPLL_ci.induct)
  case (1 Ms N) note IH = this(1) and that = this(2)
  obtain S where SN: "(S, N) = DPLL_step (Ms, N)" using DPLL_step_obtains by metis
  { assume "\<not> dpll_all_inv (toS Ms N)"
    hence ?case using that by auto
  }
  moreover {
    assume n: "(S, N) \<noteq> (Ms, N)"
    and inv: "dpll_all_inv (toS Ms N)"
    have "\<exists>ms. DPLL_step (Ms, N) = (ms, N)"
      by (metis `\<And>thesisa. (\<And>S. (S, N) = DPLL_step (Ms, N) \<Longrightarrow> thesisa) \<Longrightarrow> thesisa`)
    hence ?thesis
      using IH that by fastforce
  }
  moreover {
    assume n: "(S, N) = (Ms, N)"
    and inv: "dpll_all_inv (toS Ms N)"
    have ?case using SN n that by fastforce
 }
  ultimately show ?case by blast
qed


lemma DPLL_ci_no_more_step:
  assumes step: "DPLL_ci Ms N = (Ms', N')"
  shows "DPLL_ci Ms' N' = (Ms', N')"
  using assms
proof (induct arbitrary: Ms' N' rule: DPLL_ci.induct)
  case (1 Ms N Ms' N') note IH = this(1) and step = this(2)
  obtain S\<^sub>1 where S: "(S\<^sub>1, N) = DPLL_step (Ms, N)" using DPLL_step_obtains by auto
  { assume "\<not>dpll_all_inv (toS Ms N)"
    hence ?case using step by auto
  }
  moreover {
    assume "dpll_all_inv (toS Ms N)"
    and "(S\<^sub>1, N) = (Ms, N)"
    hence ?case using S step by auto
  }
  moreover
  { assume inv: "dpll_all_inv (toS Ms N)"
    assume n: "(S\<^sub>1, N) \<noteq> (Ms, N)"
    obtain S\<^sub>1' where SS: "(S\<^sub>1', N) = DPLL_ci S\<^sub>1 N" using DPLL_ci_obtains by blast
    moreover have "DPLL_ci Ms N = DPLL_ci S\<^sub>1 N"
      proof -
        have "(case (S\<^sub>1, N) of (ms, lss) \<Rightarrow> if (ms, lss) = (Ms, N) then (Ms, N) else DPLL_ci ms N)
          = DPLL_ci Ms N"
          using S DPLL_ci.simps[of Ms N] calculation inv by presburger
        hence "(if (S\<^sub>1, N) = (Ms, N) then (Ms, N) else DPLL_ci S\<^sub>1 N) = DPLL_ci Ms N"
          by fastforce
        thus ?thesis
          using calculation n by presburger
      qed
    moreover
      have "DPLL_ci S\<^sub>1' N = (S\<^sub>1', N)" using step IH[OF _ _ S n SS[symmetric]] inv by blast
    ultimately have ?case using step by fastforce
  }
  ultimately show ?case by blast
qed


lemma DPLL_part_dpll_all_inv_final:
  fixes M Ms':: "(int, dpll_marked_level, dpll_mark) marked_lit list" and
    N :: "int literal list list"
  assumes inv: "dpll_all_inv (Ms, set (map mset N))"
  and MsN: "DPLL_part Ms N = (Ms', N)"
  shows "final_dpll_state (toS Ms' N) \<and> dpll\<^sup>*\<^sup>* (toS Ms N) (toS Ms' N)"
proof -
  have 2: "DPLL_ci Ms N = DPLL_part Ms N" using inv dpll_all_inv_implieS_2_eq3_and_dom by blast
  hence star: "dpll\<^sup>*\<^sup>* (toS Ms N) (toS Ms' N)" unfolding MsN using DPLL_ci_dpll_rtranclp by blast
  hence inv': "dpll_all_inv (toS Ms' N)" using inv rtranclp_dpll_all_inv by blast
  show ?thesis using star DPLL_ci_final_state[OF DPLL_ci_no_more_step inv'] 2 unfolding MsN by blast
qed

subsubsection \<open>Embedding the invariant into the type\<close>
paragraph \<open>Defining the type\<close>
typedef dpll_state =
    "{(M::(int, dpll_marked_level, dpll_mark) marked_lit list, N::int literal list list).
        dpll_all_inv (toS M N)}"
  morphisms rough_state_of state_of
proof
    show "([],[]) \<in> {(M, N). dpll_all_inv (toS M N)}" by (auto simp add: dpll_all_inv_def)
qed

lemma
  assumes "finite (set (map mset N))"
  shows "DPLL_part_dom ([], N)"
  using assms  dpll_all_inv_implieS_2_eq3_and_dom[of "[]" N] by (simp add: dpll_all_inv_def)

paragraph \<open>Some type classes\<close>
instantiation dpll_state :: equal
begin
definition equal_dpll_state :: "dpll_state \<Rightarrow> dpll_state \<Rightarrow> bool" where
 "equal_dpll_state S S' = (rough_state_of S = rough_state_of S')"
instance
  by standard (simp add: rough_state_of_inject equal_dpll_state_def)
end

paragraph \<open>DPLL\<close>
definition DPLL_step' :: "dpll_state \<Rightarrow> dpll_state" where
  "DPLL_step' S = state_of (DPLL_step (rough_state_of S))"

declare rough_state_of_inverse[simp]

lemma DPLL_step_dpll_conc_inv:
  "DPLL_step (rough_state_of S) \<in> {(M, N). dpll_all_inv (toS M N)}"
  by (smt DPLL_ci.simps DPLL_ci_dpll_rtranclp case_prodE case_prodI2 rough_state_of
    mem_Collect_eq old.prod.case prod.sel(2) rtranclp_dpll_all_inv snd_DPLL_step)

lemma rough_state_of_DPLL_step'_DPLL_step[simp]:
  "rough_state_of (DPLL_step' S) = DPLL_step (rough_state_of S)"
  using DPLL_step_dpll_conc_inv DPLL_step'_def state_of_inverse by auto

function DPLL_tot:: "dpll_state \<Rightarrow> dpll_state" where
"DPLL_tot S =
  (let S' = DPLL_step' S in
   if S' = S then S else DPLL_tot S')"
  by fast+
termination
proof (relation "{(T', T).
     (rough_state_of T', rough_state_of T)
        \<in> {(S', S). (toS' S', toS' S)
              \<in> {(S', S). dpll_all_inv S \<and> dpll S S'}}}")
  show "wf {(b, a).
          (rough_state_of b, rough_state_of a)
            \<in> {(b, a). (toS' b, toS' a)
              \<in> {(b, a). dpll_all_inv a \<and> dpll a b}}}"
    using  wf_if_measure_f[OF wf_if_measure_f[OF dpll_wf, of "toS'"], of rough_state_of] .
next
  fix S x
  assume x: "x = DPLL_step' S"
  and "x \<noteq> S"
  have "dpll_all_inv (case rough_state_of S of (Ms, N) \<Rightarrow> (Ms, mset ` set N))"
    by (metis (no_types, lifting) case_prodE rough_state_of mem_Collect_eq old.prod.case set_map)
  moreover have "dpll (case rough_state_of S of (Ms, N) \<Rightarrow> (Ms, mset ` set N))
                      (case rough_state_of (DPLL_step' S) of (Ms, N) \<Rightarrow> (Ms, mset ` set N))"
    proof -
      obtain Ms N where Ms: "(Ms, N) = rough_state_of S" by (cases "rough_state_of S") auto
      have "dpll_all_inv (toS' (Ms, N))" unfolding Ms by (simp add: calculation)
      moreover obtain Ms' N' where Ms': "(Ms', N') = rough_state_of (DPLL_step' S)"
        by (cases "rough_state_of (DPLL_step' S)") auto
      ultimately have "dpll_all_inv (toS' (Ms', N'))" unfolding Ms'
        by (metis (no_types, lifting) case_prod_unfold mem_Collect_eq rough_state_of)

      have "dpll (toS Ms N) (toS Ms' N')"
        apply (rule DPLL_step_is_a_dpll_step[of Ms' N' Ms N])
        unfolding Ms Ms' using `x \<noteq> S` rough_state_of_inject x by fastforce+
      thus ?thesis unfolding Ms[symmetric] Ms'[symmetric] by auto
    qed
  ultimately show "(x, S) \<in> {(T', T). (rough_state_of T', rough_state_of T)
    \<in> {(S', S). (toS' S', toS' S) \<in> {(S', S). dpll_all_inv S \<and> dpll S S'}}}"
    by (auto simp add: x)
qed

lemma [code]:
"DPLL_tot S =
  (let S' = DPLL_step' S in
   if S' = S then S else DPLL_tot S')" by auto


lemma DPLL_tot_DPLL_step_DPLL_tot[simp]: "DPLL_tot (DPLL_step' S) = DPLL_tot S"
  apply (case_tac "DPLL_step' S = S")
  apply simp
  unfolding DPLL_tot.simps[of S] by (simp del: DPLL_tot.simps)

lemma DOPLL_step'_DPLL_tot[simp]:
  "DPLL_step' (DPLL_tot S) = DPLL_tot S"
  by (rule  DPLL_tot.induct[of "\<lambda>S. DPLL_step' (DPLL_tot S) = DPLL_tot S" S])
     (metis (full_types) DPLL_tot.simps)
(*
why does this not work?
proof (induction arbitrary: S rule: DPLL_tot.induct)
  case (1 S') note IH = this(1)
  show ?case
    proof cases
      assume "DPLL_step' S = S"
      thus ?thesis by auto
    next
      assume "DPLL_step' S \<noteq> S"
      thus ?thesis using IH
*)


lemma DPLL_tot_final_state:
  assumes "DPLL_tot S = S"
  shows "final_dpll_state (toS' (rough_state_of S))"
proof -
  have "DPLL_step' S =  S" using assms[symmetric] DOPLL_step'_DPLL_tot by metis
  hence "DPLL_step (rough_state_of S) =  (rough_state_of S)"
    unfolding DPLL_step'_def using DPLL_step_dpll_conc_inv rough_state_of_inverse
    by (metis rough_state_of_DPLL_step'_DPLL_step)
  thus ?thesis
    by (metis (mono_tags, lifting) DPLL_step_stuck_final_state old.prod.exhaust split_conv)
qed

lemma DPLL_tot_star:
  assumes "rough_state_of (DPLL_tot S) = S'"
  shows "dpll\<^sup>*\<^sup>* (toS' (rough_state_of S)) (toS' S')"
  using assms
proof (induction arbitrary: S' rule: DPLL_tot.induct)
  case (1 S S')
  let ?x = "DPLL_step' S"
  { assume "?x = S"
    then have ?case using 1(2) by simp
  }
  moreover {
    assume S: "?x \<noteq> S"
    have ?case
      by (smt "1.IH" "1.prems" DPLL_step_is_a_dpll_step DPLL_tot.simps
        rough_state_of_DPLL_step'_DPLL_step rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl
        rtranclp_idemp case_prodE2 split_conv)
  }
  ultimately show ?case by auto
qed

lemma rough_state_of_rough_state_of_nil[simp]:
  "rough_state_of (state_of ([], N)) = ([], N)"
  apply (rule DPLL_Implementation.dpll_state.state_of_inverse)
  unfolding dpll_all_inv_def by auto

text \<open>Theorem of correctness\<close>
lemma DPLL_tot_correct:
  assumes "rough_state_of (DPLL_tot (state_of (([], N)))) = (M, N')"
  and "(M', N'') =  toS' (M, N')"
  shows "M' \<Turnstile>as N'' \<longleftrightarrow> satisfiable N''"
proof -
  have "dpll\<^sup>*\<^sup>* (toS' ([], N)) (toS' (M, N'))" using DPLL_tot_star[OF assms(1)] by auto
  moreover have "final_dpll_state (toS' (M, N'))"
    using DPLL_tot_final_state by (metis (mono_tags, lifting) DOPLL_step'_DPLL_tot DPLL_tot.simps
      assms(1))
  moreover have "finite (set (map mset N))" by auto
  ultimately show ?thesis using dpll_completeness' by (smt DPLL_ci.simps DPLL_ci_dpll_rtranclp
    assms(2) dpll_all_inv_def prod.case prod.sel(1) prod.sel(2) rtranclp_dpll_inv(3)
    rtranclp_dpll_inv_starting_from_0)
qed

subsection \<open>Code export\<close>
subsubsection \<open>A conversion to @{typ dpll_state}\<close>
definition Con :: "(int, dpll_marked_level, dpll_mark) marked_lit list \<times> int literal list list
                     \<Rightarrow> dpll_state" where
  "Con xs = state_of (if dpll_all_inv (toS (fst xs) (snd xs)) then xs else ([], []))"
lemma [code abstype]:
 "Con (rough_state_of S) = S"
  using rough_state_of[of S] unfolding Con_def by auto

  declare rough_state_of_DPLL_step'_DPLL_step[code abstract]

lemma [simp]:
  "Con (DPLL_step (rough_state_of s)) = state_of (DPLL_step (rough_state_of s))"
  unfolding Con_def by (metis (mono_tags, lifting) DPLL_step_dpll_conc_inv mem_Collect_eq
    prod.case_eq_if)

text \<open>A slightly different version of @{term DPLL_tot} where the returned boolean indicates the
  result.\<close>
definition DPLL_tot_rep where
"DPLL_tot_rep S =
  (let (M, N) = (rough_state_of (DPLL_tot S)) in (\<forall>A \<in> set N. (\<exists>a\<in>set A. a \<in> lits_of (M)), M))"

text \<open>One version of the generated SML code is here, but not included in the generated document.
  The only differences are:
  \<^item> export @{typ "'a literal"}from the SML Module;
  \<^item> export the constructor @{term Con};
  \<^item> export the @{term int} constructor.

  All these allows to test on the code on some examples.
  \<close>

(*<*)
export_code DPLL_tot_rep in SML
ML {*

structure HOL : sig
  type 'a equal
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

end; (*struct HOL*)

structure List : sig
  val equal_list : 'a HOL.equal -> ('a list) HOL.equal
  val find : ('a -> bool) -> 'a list -> 'a option
  val filter : ('a -> bool) -> 'a list -> 'a list
  val member : 'a HOL.equal -> 'a list -> 'a -> bool
  val list_ex : ('a -> bool) -> 'a list -> bool
  val remove1 : 'a HOL.equal -> 'a -> 'a list -> 'a list
  val map : ('a -> 'b) -> 'a list -> 'b list
  val pred_list : ('a -> bool) -> 'a list -> bool
end = struct

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    HOL.eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) HOL.equal;

fun find uu [] = NONE
  | find p (x :: xs) = (if p x then SOME x else find p xs);

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun member A_ [] y = false
  | member A_ (x :: xs) y = HOL.eq A_ x y orelse member A_ xs y;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun remove1 A_ x [] = []
  | remove1 A_ x (y :: xs) =
    (if HOL.eq A_ x y then xs else y :: remove1 A_ x xs);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun pred_list p [] = true
  | pred_list p (x :: xs) = p x andalso pred_list p xs;

end; (*struct List*)

structure Set : sig
  datatype 'a set = Set of 'a list | Coset of 'a list
  val image : ('a -> 'b) -> 'a set -> 'b set
  val member : 'a HOL.equal -> 'a -> 'a set -> bool
end = struct

datatype 'a set = Set of 'a list | Coset of 'a list;

fun image f (Set xs) = Set (List.map f xs);

fun member A_ x (Coset xs) = not (List.member A_ xs x)
  | member A_ x (Set xs) = List.member A_ xs x;

end; (*struct Set*)

structure Arith : sig
  datatype int = Int_of_integer of IntInf.int;
  val equal_int : int HOL.equal
end = struct

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

val equal_int = {equal = equal_inta} : int HOL.equal;

end; (*struct Arith*)

structure Propo_DPLL : sig
  datatype dpll_mark = Proped
  val equal_dpll_mark : dpll_mark HOL.equal
  datatype dpll_marked_level = Level
  val equal_dpll_marked_level : dpll_marked_level HOL.equal
end = struct

datatype dpll_mark = Proped;

fun equal_dpll_marka Proped Proped = true;

val equal_dpll_mark = {equal = equal_dpll_marka} : dpll_mark HOL.equal;

datatype dpll_marked_level = Level;

fun equal_dpll_marked_levela Level Level = true;

val equal_dpll_marked_level = {equal = equal_dpll_marked_levela} :
  dpll_marked_level HOL.equal;

end; (*struct Propo_DPLL*)

structure Product_Type : sig
  val apfst : ('a -> 'b) -> 'a * 'c -> 'b * 'c
  val equal_prod : 'a HOL.equal -> 'b HOL.equal -> 'a * 'b -> 'a * 'b -> bool
end = struct

fun apfst f (x, y) = (f x, y);

fun equal_prod A_ B_ (x1, x2) (y1, y2) =
  HOL.eq A_ x1 y1 andalso HOL.eq B_ x2 y2;

end; (*struct Product_Type*)

structure Clausal_Logic : sig
  datatype 'a literal = Pos of 'a | Neg of 'a;
  val equal_literala : 'a HOL.equal -> 'a literal -> 'a literal -> bool
  val equal_literal : 'a HOL.equal -> 'a literal HOL.equal
  val atm_of : 'a literal -> 'a
  val uminus_literal : 'a literal -> 'a literal
end = struct

datatype 'a literal = Pos of 'a | Neg of 'a;

fun equal_literala A_ (Pos x1) (Neg x2) = false
  | equal_literala A_ (Neg x2) (Pos x1) = false
  | equal_literala A_ (Neg x2) (Neg y2) = HOL.eq A_ x2 y2
  | equal_literala A_ (Pos x1) (Pos y1) = HOL.eq A_ x1 y1;

fun equal_literal A_ = {equal = equal_literala A_} : 'a literal HOL.equal;

fun atm_of (Pos x1) = x1
  | atm_of (Neg x2) = x2;

fun is_pos (Pos x1) = true
  | is_pos (Neg x2) = false;

fun uminus_literal l = (if is_pos l then Neg else Pos) (atm_of l);

end; (*struct Clausal_Logic*)

structure Partial_Annotated_Clausal_Logic : sig
  datatype ('a, 'b, 'c) marked_lit = Marked of 'a Clausal_Logic.literal * 'b |
    Propagated of 'a Clausal_Logic.literal * 'c
  val equal_marked_lit :
    'a HOL.equal -> 'b HOL.equal -> 'c HOL.equal ->
      ('a, 'b, 'c) marked_lit HOL.equal
  val lit_of : ('a, 'b, 'c) marked_lit -> 'a Clausal_Logic.literal
  val lits_of : ('a, 'b, 'c) marked_lit list -> 'a Clausal_Logic.literal Set.set
  val backtrack_split :
    ('a, 'b, 'c) marked_lit list ->
      ('a, 'b, 'c) marked_lit list * ('a, 'b, 'c) marked_lit list
end = struct

datatype ('a, 'b, 'c) marked_lit = Marked of 'a Clausal_Logic.literal * 'b |
  Propagated of 'a Clausal_Logic.literal * 'c;

fun equal_marked_lita A_ B_ C_ (Marked (x11, x12)) (Propagated (x21, x22)) =
  false
  | equal_marked_lita A_ B_ C_ (Propagated (x21, x22)) (Marked (x11, x12)) =
    false
  | equal_marked_lita A_ B_ C_ (Propagated (x21, x22)) (Propagated (y21, y22)) =
    Clausal_Logic.equal_literala A_ x21 y21 andalso HOL.eq C_ x22 y22
  | equal_marked_lita A_ B_ C_ (Marked (x11, x12)) (Marked (y11, y12)) =
    Clausal_Logic.equal_literala A_ x11 y11 andalso HOL.eq B_ x12 y12;

fun equal_marked_lit A_ B_ C_ = {equal = equal_marked_lita A_ B_ C_} :
  ('a, 'b, 'c) marked_lit HOL.equal;

fun lit_of (Marked (x11, x12)) = x11
  | lit_of (Propagated (x21, x22)) = x21;

fun lits_of ls = Set.image lit_of (Set.Set ls);

fun backtrack_split [] = ([], [])
  | backtrack_split (Propagated (l, p) :: mlits) =
    Product_Type.apfst (fn a => Propagated (l, p) :: a) (backtrack_split mlits)
  | backtrack_split (Marked (la, l) :: mlits) = ([], Marked (la, l) :: mlits);

end; (*struct Partial_Annotated_Clausal_Logic*)

structure DPLL_Implementation : sig
  datatype dpll_state =
    Con of
      ((Arith.int, Propo_DPLL.dpll_marked_level, Propo_DPLL.dpll_mark)
         Partial_Annotated_Clausal_Logic.marked_lit list *
        (Arith.int Clausal_Logic.literal list) list);

  val dPLL_tot_rep : dpll_state -> bool * (Arith.int, Propo_DPLL.dpll_marked_level, Propo_DPLL.dpll_mark) Partial_Annotated_Clausal_Logic.marked_lit list
end = struct

datatype dpll_state =
  Con of
    ((Arith.int, Propo_DPLL.dpll_marked_level, Propo_DPLL.dpll_mark)
       Partial_Annotated_Clausal_Logic.marked_lit list *
      (Arith.int Clausal_Logic.literal list) list);

fun rough_state_of (Con x) = x;

fun equal_dpll_state sa s =
  Product_Type.equal_prod
    (List.equal_list
      (Partial_Annotated_Clausal_Logic.equal_marked_lit Arith.equal_int
        Propo_DPLL.equal_dpll_marked_level Propo_DPLL.equal_dpll_mark))
    (List.equal_list
      (List.equal_list (Clausal_Logic.equal_literal Arith.equal_int)))
    (rough_state_of sa) (rough_state_of s);

fun is_unit_clause_code A_ l m =
  (case List.filter
          (fn a =>
            not (Set.member A_ (Clausal_Logic.atm_of a)
                  (Set.image Clausal_Logic.atm_of
                    (Partial_Annotated_Clausal_Logic.lits_of m))))
          l
    of [] => NONE
    | [a] =>
      (if List.pred_list
            (fn c =>
              Set.member (Clausal_Logic.equal_literal A_)
                (Clausal_Logic.uminus_literal c)
                (Partial_Annotated_Clausal_Logic.lits_of m))
            (List.remove1 (Clausal_Logic.equal_literal A_) a l)
        then SOME a else NONE)
    | _ :: _ :: _ => NONE);

fun is_unit_clause A_ l m = is_unit_clause_code A_ l m;

fun find_first_unit_clause A_ (a :: l) m =
  (case is_unit_clause A_ a m of NONE => find_first_unit_clause A_ l m
    | SOME aa => SOME aa)
  | find_first_unit_clause A_ [] uu = NONE;

fun find_first_unused_var (a :: l) m =
  (case List.find
          (fn lit =>
            not (Set.member (Clausal_Logic.equal_literal Arith.equal_int) lit
                  m) andalso
              not (Set.member (Clausal_Logic.equal_literal Arith.equal_int)
                    (Clausal_Logic.uminus_literal lit) m))
          a
    of NONE => find_first_unused_var l m | SOME aa => SOME aa)
  | find_first_unused_var [] uu = NONE;

fun dPLL_step x =
  (fn (ms, n) =>
    (case find_first_unit_clause Arith.equal_int n ms
      of NONE =>
        (if List.list_ex
              (List.pred_list
                (fn c =>
                  Set.member (Clausal_Logic.equal_literal Arith.equal_int)
                    (Clausal_Logic.uminus_literal c)
                    (Partial_Annotated_Clausal_Logic.lits_of ms)))
              n
          then (case Partial_Annotated_Clausal_Logic.backtrack_split ms
                 of (_, []) => (ms, n)
                 | (_, l :: m) =>
                   (Partial_Annotated_Clausal_Logic.Propagated
                      (Clausal_Logic.uminus_literal
                         (Partial_Annotated_Clausal_Logic.lit_of l),
                        Propo_DPLL.Proped) ::
                      m,
                     n))
          else (case find_first_unused_var n
                       (Partial_Annotated_Clausal_Logic.lits_of ms)
                 of NONE => (ms, n)
                 | SOME a =>
                   (Partial_Annotated_Clausal_Logic.Marked
                      (a, Propo_DPLL.Level) ::
                      ms,
                     n)))
      | SOME l =>
        (Partial_Annotated_Clausal_Logic.Propagated (l, Propo_DPLL.Proped) ::
           ms,
          n)))
    x;

fun dPLL_stepa s = Con (dPLL_step (rough_state_of s));

fun dPLL_tot s =
  let
    val sa = dPLL_stepa s;
  in
    (if equal_dpll_state sa s then s else dPLL_tot sa)
  end;

fun dPLL_tot_rep s =
  let
    val a = rough_state_of (dPLL_tot s);
    val (m, aa) = a;
  in
    (List.pred_list
      (List.list_ex
        (fn ab =>
          Set.member (Clausal_Logic.equal_literal Arith.equal_int) ab
            (Partial_Annotated_Clausal_Logic.lits_of m)))
      aa,
      m)
  end;

end; (*struct DPLL_Implementation*)


*}

ML {*
open Clausal_Logic;
open DPLL_Implementation;
open Arith;
let
  val P = Int_of_integer 1
  val Q = Int_of_integer 2
  val R = Int_of_integer 3
  val S = Int_of_integer 4
  val T = Int_of_integer 5
  val U = Int_of_integer 6
  val N = [[Neg P, Pos Q], [Neg R, Pos S], [Neg T, Neg U], [Neg R, Neg T, Pos U]]
in
 DPLL_Implementation.dPLL_tot_rep (Con ([], N))

end
*}
ML {*
open Clausal_Logic;
open DPLL_Implementation;
open Arith;
let
  val P = Int_of_integer 1
  val Q = Int_of_integer 2
  val R = Int_of_integer 3
  val S = Int_of_integer 4
  val T = Int_of_integer 5
  val N = [[Pos P, Pos Q, Pos R],
           [Pos P,        Neg R],
           [Neg P,             Pos S],
           [Neg P,                    Pos T],
           [       Pos Q,      Neg S, Neg T],
           [       Neg Q]]
in
 DPLL_Implementation.dPLL_tot_rep (Con ([], N))
end
*}

ML {*
open Clausal_Logic;
open DPLL_Implementation;
open Arith;
let
  val P = Int_of_integer 1
  val Q = Int_of_integer 2
  val R = Int_of_integer 3
  val S = Int_of_integer 4
  val T = Int_of_integer 5
  val N = [[Pos P, Pos Q, Pos R],
           [Pos P,        Neg R],
           [Neg P,             Pos S],
           [Neg P,                    Pos T],
           [       Pos Q,      Neg S, Neg T],
           [       Neg Q]]
in
 DPLL_Implementation.dPLL_tot_rep (Con ([], N))
end
*}
declare[[ML_print_depth=100]]
ML {*
open Clausal_Logic;
open DPLL_Implementation;
open Arith;
let
  val a = Int_of_integer 10
  val b = Int_of_integer 20
  val c = Int_of_integer 1
  val d = Int_of_integer 40
  val e = Int_of_integer 50
  val f = Int_of_integer 2
  val g = Int_of_integer 60
  val N = [[Pos a, Pos b],
           [       Neg b, Pos c, Pos d],
           [       Neg b,               Pos e],
           [                     Neg d, Neg e, Pos f],
           [Neg a,                                    Pos g],
           [       Pos b,                             Neg g]]
in
 DPLL_Implementation.dPLL_tot_rep (Con ([], N))
end
*}

(*>*)
end
