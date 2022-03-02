theory DPLL_W_Implementation
imports DPLL_CDCL_W_Implementation DPLL_W "HOL-Library.Code_Target_Numeral"
begin

subsection \<open>Simple Implementation of DPLL\<close>

subsubsection \<open>Combining the propagate and decide: a DPLL step\<close>

definition DPLL_step :: "int dpll\<^sub>W_ann_lits \<times> int literal list list
  \<Rightarrow> int dpll\<^sub>W_ann_lits \<times> int literal list list" where
"DPLL_step = (\<lambda>(Ms, N).
  (case find_first_unit_clause N Ms of
    Some (L, _) \<Rightarrow> (Propagated L () # Ms, N)
  | _ \<Rightarrow>
    if \<exists>C \<in> set N. (\<forall>c \<in> set C. -c \<in> lits_of_l Ms)
    then
      (case backtrack_split Ms of
        (_, L # M) \<Rightarrow> (Propagated (- (lit_of L)) () # M, N)
      | (_, _) \<Rightarrow> (Ms, N)
      )
    else
    (case find_first_unused_var N (lits_of_l Ms) of
        Some a \<Rightarrow> (Decided a # Ms, N)
      | None \<Rightarrow> (Ms, N))))"

text \<open>Example of propagation:\<close>
value "DPLL_step ([Decided (Neg 1)], [[Pos (1::int), Neg 2]])"

text \<open>We define the conversion function between the states as defined in \<open>Prop_DPLL\<close> (with
  multisets) and here (with lists).\<close>
abbreviation "toS \<equiv> \<lambda>(Ms::(int, unit) ann_lits)
                      (N:: int literal list list). (Ms, mset (map mset N)) "
abbreviation "toS' \<equiv> \<lambda>(Ms::(int, unit) ann_lits,
                          N:: int literal list list). (Ms, mset (map mset N)) "

text \<open>Proof of correctness of @{term DPLL_step}\<close>
lemma DPLL_step_is_a_dpll\<^sub>W_step:
  assumes step: "(Ms', N') = DPLL_step (Ms, N)"
  and neq: "(Ms, N) \<noteq> (Ms', N')"
  shows "dpll\<^sub>W (toS Ms N) (toS Ms' N')"
proof -
  let ?S = "(Ms, mset (map mset N))"
  { fix L E
    assume unit: "find_first_unit_clause N Ms = Some (L, E)"
    then have Ms'N: "(Ms', N') = (Propagated L () # Ms, N)"
      using step unfolding DPLL_step_def by auto
    obtain C where
      C: "C \<in> set N" and
      Ms: "Ms \<Turnstile>as CNot (mset C - {#L#})" and
      undef: "undefined_lit Ms L" and
      "L \<in> set C" using find_first_unit_clause_some[OF unit] by metis
    have "dpll\<^sub>W (Ms, mset (map mset N))
         (Propagated L () # fst (Ms, mset (map mset N)), snd (Ms, mset (map mset N)))"
      apply (rule dpll\<^sub>W.propagate)
      using Ms undef C \<open>L \<in> set C\<close> by (auto simp add: C)
    then have ?thesis using Ms'N by auto
  }
  moreover
  { assume unit: "find_first_unit_clause N Ms = None"
    assume exC: "\<exists>C \<in> set N. Ms \<Turnstile>as CNot (mset C)"
    then obtain C where C: "C \<in> set N" and Ms: "Ms \<Turnstile>as CNot (mset C)" by auto
    then obtain L M M' where bt: "backtrack_split Ms = (M', L # M)"
      using step exC neq unfolding DPLL_step_def prod.case unit
      by (cases "backtrack_split Ms", rename_tac b, case_tac b) (auto simp: lits_of_l_unfold)
    then have "is_decided L" using backtrack_split_snd_hd_decided[of Ms] by auto
    have 1: "dpll\<^sub>W (Ms, mset (map mset N))
                  (Propagated (- lit_of L) () # M, snd (Ms, mset (map mset N)))"
      apply (rule dpll\<^sub>W.backtrack[OF _ \<open>is_decided L\<close>, of ])
      using C Ms bt by auto
    moreover have "(Ms', N') = (Propagated (- (lit_of L)) () # M, N)"
      using step exC unfolding DPLL_step_def bt prod.case unit by (auto simp: lits_of_l_unfold)
    ultimately have ?thesis by auto
  }
  moreover
  { assume unit: "find_first_unit_clause N Ms = None"
    assume exC: "\<not> (\<exists>C \<in> set N. Ms \<Turnstile>as CNot (mset C))"
    obtain L where unused: "find_first_unused_var N (lits_of_l Ms) = Some L"
      using step exC neq unfolding DPLL_step_def prod.case unit
      by (cases "find_first_unused_var N (lits_of_l Ms)") (auto simp: lits_of_l_unfold)
    have "dpll\<^sub>W (Ms, mset (map mset N))
               (Decided L # fst (Ms, mset (map mset N)), snd (Ms, mset (map mset N)))"
      apply (rule dpll\<^sub>W.decided[of ?S L])
      using find_first_unused_var_Some[OF unused]
      by (auto simp add: Decided_Propagated_in_iff_in_lits_of_l atms_of_ms_def)
    moreover have "(Ms', N') = (Decided L # Ms, N)"
      using step exC unfolding DPLL_step_def unused prod.case unit by (auto simp: lits_of_l_unfold)
    ultimately have ?thesis by auto
  }
  ultimately show ?thesis by (cases "find_first_unit_clause N Ms") auto
qed

lemma DPLL_step_stuck_final_state:
  assumes step: "(Ms, N) = DPLL_step (Ms, N)"
  shows "conclusive_dpll\<^sub>W_state (toS Ms N)"
proof -
  have unit: "find_first_unit_clause N Ms = None"
    using step unfolding DPLL_step_def by (auto split:option.splits)

  { assume n: "\<exists>C \<in> set N. Ms \<Turnstile>as CNot (mset C)"
    then have Ms: "(Ms, N) = (case backtrack_split Ms of (x, []) \<Rightarrow> (Ms, N)
                         | (x, L # M) \<Rightarrow> (Propagated (- lit_of L) () # M, N))"
      using step unfolding DPLL_step_def by (simp add: unit lits_of_l_unfold)

  have "snd (backtrack_split Ms) = []"
    proof (cases "backtrack_split Ms", cases "snd (backtrack_split Ms)")
      fix a b
      assume "backtrack_split Ms = (a, b)" and "snd (backtrack_split Ms) = []"
      then show "snd (backtrack_split Ms) = []" by blast
    next
      fix a b aa list
      assume
        bt: "backtrack_split Ms = (a, b)" and
        bt': "snd (backtrack_split Ms) = aa # list"
      then have Ms: "Ms = Propagated (- lit_of aa) () # list" using Ms by auto
      have "is_decided aa" using backtrack_split_snd_hd_decided[of Ms] bt bt' by auto
      moreover have "fst (backtrack_split Ms) @ aa # list = Ms"
        using backtrack_split_list_eq[of Ms] bt' by auto
      ultimately have False unfolding Ms by auto
      then show "snd (backtrack_split Ms) = []" by blast
    qed

    then have ?thesis
      using n backtrack_snd_empty_not_decided[of Ms] unfolding conclusive_dpll\<^sub>W_state_def
      by (cases "backtrack_split Ms") auto
  }
  moreover {
    assume n: "\<not> (\<exists>C \<in> set N. Ms \<Turnstile>as CNot (mset C))"
    then have "find_first_unused_var N (lits_of_l Ms) = None"
      using step unfolding DPLL_step_def by (simp add: unit lits_of_l_unfold split: option.splits)
    then have a: "\<forall>a \<in> set N. atm_of ` set a \<subseteq> atm_of ` (lits_of_l Ms)" by auto
    have "fst (toS Ms N) \<Turnstile>asm snd (toS Ms N)" unfolding true_annots_def CNot_def Ball_def
      proof clarify
        fix x
        assume x: "x \<in> set_mset (clauses (toS Ms N))"
        then have "\<not>Ms \<Turnstile>as CNot x" using n unfolding true_annots_def CNot_def Ball_def by auto
        moreover have "total_over_m (lits_of_l Ms) {x}"
          using a x image_iff in_mono atms_of_s_def
          unfolding total_over_m_def total_over_set_def lits_of_def by fastforce
        ultimately show "fst (toS Ms N) \<Turnstile>a x"
          using total_not_CNot[of "lits_of_l Ms" x] by (simp add: true_annot_def true_annots_true_cls)
      qed
    then have ?thesis unfolding conclusive_dpll\<^sub>W_state_def by blast
  }
  ultimately show ?thesis by blast
qed

subsubsection \<open>Adding invariants\<close>
paragraph \<open>Invariant tested in the function\<close>
function DPLL_ci :: "int dpll\<^sub>W_ann_lits \<Rightarrow> int literal list list
  \<Rightarrow> int dpll\<^sub>W_ann_lits \<times> int literal list list" where
"DPLL_ci Ms N =
  (if \<not>dpll\<^sub>W_all_inv (Ms, mset (map mset N))
  then (Ms, N)
  else
   let (Ms', N') = DPLL_step (Ms, N) in
   if (Ms', N') = (Ms, N) then (Ms, N) else DPLL_ci Ms' N)"
  by fast+
termination
proof (relation "{(S', S).  (toS' S', toS' S) \<in> {(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W S S'}}")
  show "wf {(S', S).(toS' S', toS' S) \<in> {(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W S S'}}"
    using wf_if_measure_f[OF wf_dpll\<^sub>W, of "toS'"] by auto
next
  fix Ms :: "int dpll\<^sub>W_ann_lits" and N x xa y
  assume"\<not> \<not> dpll\<^sub>W_all_inv (toS Ms N)"
  and step: "x = DPLL_step (Ms, N)"
  and x: "(xa, y) = x"
  and "(xa, y) \<noteq> (Ms, N)"
  then show "((xa, N), Ms, N) \<in> {(S', S). (toS' S', toS' S) \<in> {(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W S S'}}"
    using DPLL_step_is_a_dpll\<^sub>W_step dpll\<^sub>W_same_clauses split_conv by fastforce
qed

paragraph \<open>No invariant tested\<close>
function (domintros) DPLL_part:: "int dpll\<^sub>W_ann_lits \<Rightarrow> int literal list list \<Rightarrow>
  int dpll\<^sub>W_ann_lits \<times> int literal list list" where
"DPLL_part Ms N =
  (let (Ms', N') = DPLL_step (Ms, N) in
   if (Ms', N') = (Ms, N) then (Ms, N) else DPLL_part Ms' N)"
  by fast+

lemma snd_DPLL_step[simp]:
  "snd (DPLL_step (Ms, N)) = N"
  unfolding DPLL_step_def by (auto split: if_split option.splits prod.splits list.splits)

lemma dpll\<^sub>W_all_inv_implieS_2_eq3_and_dom:
  assumes "dpll\<^sub>W_all_inv (Ms, mset (map mset N))"
  shows "DPLL_ci Ms N = DPLL_part Ms N \<and> DPLL_part_dom (Ms, N)"
  using assms
proof (induct rule: DPLL_ci.induct)
  case (1 Ms N)
  have "snd (DPLL_step (Ms, N)) = N" by auto
  then obtain Ms' where Ms': "DPLL_step (Ms, N) = (Ms', N)" by (cases "DPLL_step (Ms, N)") auto
  have inv': "dpll\<^sub>W_all_inv (toS Ms' N)" by (metis (mono_tags) "1.prems" DPLL_step_is_a_dpll\<^sub>W_step
    Ms' dpll\<^sub>W_all_inv old.prod.inject)
  { assume "(Ms', N) \<noteq> (Ms, N)"
    then have "DPLL_ci Ms' N = DPLL_part Ms' N \<and> DPLL_part_dom (Ms', N)" using 1(1)[of _ Ms' N] Ms'
      1(2) inv' by auto
    then have "DPLL_part_dom (Ms, N)" using DPLL_part.domintros Ms' by fastforce
    moreover have "DPLL_ci Ms N = DPLL_part Ms N" using "1.prems" DPLL_part.psimps Ms'
      \<open>DPLL_ci Ms' N = DPLL_part Ms' N \<and> DPLL_part_dom (Ms', N)\<close> \<open>DPLL_part_dom (Ms, N)\<close> by auto
    ultimately have ?case by blast
  }
  moreover {
    assume "(Ms', N) = (Ms, N)"
    then have ?case using DPLL_part.domintros DPLL_part.psimps Ms' by fastforce
  }
  ultimately show ?case by blast
qed

lemma DPLL_ci_dpll\<^sub>W_rtranclp:
  assumes "DPLL_ci Ms N = (Ms', N')"
  shows "dpll\<^sub>W\<^sup>*\<^sup>* (toS Ms N) (toS Ms' N)"
  using assms
proof (induct Ms N arbitrary: Ms' N' rule: DPLL_ci.induct)
  case (1 Ms N Ms' N') note IH = this(1) and step = this(2)
  obtain S\<^sub>1 S\<^sub>2 where S: "(S\<^sub>1, S\<^sub>2) = DPLL_step (Ms, N)" by (cases "DPLL_step (Ms, N)") auto

  { assume "\<not>dpll\<^sub>W_all_inv (toS Ms N)"
    then have "(Ms, N) = (Ms', N)" using step by auto
    then have ?case by auto
  }
  moreover
  { assume "dpll\<^sub>W_all_inv (toS Ms N)"
    and "(S\<^sub>1, S\<^sub>2) = (Ms, N)"
    then have ?case using S step by auto
  }
  moreover
  { assume "dpll\<^sub>W_all_inv (toS Ms N)"
    and "(S\<^sub>1, S\<^sub>2) \<noteq> (Ms, N)"
    moreover obtain S\<^sub>1' S\<^sub>2' where "DPLL_ci S\<^sub>1 N = (S\<^sub>1', S\<^sub>2')" by (cases "DPLL_ci S\<^sub>1 N") auto
    moreover have "DPLL_ci Ms N = DPLL_ci S\<^sub>1 N" using DPLL_ci.simps[of Ms N] calculation
      proof -
        have "(case (S\<^sub>1, S\<^sub>2) of (ms, lss) \<Rightarrow>
          if (ms, lss) = (Ms, N) then (Ms, N) else DPLL_ci ms N) = DPLL_ci Ms N"
          using S DPLL_ci.simps[of Ms N] calculation by presburger
        then have "(if (S\<^sub>1, S\<^sub>2) = (Ms, N) then (Ms, N) else DPLL_ci S\<^sub>1 N) = DPLL_ci Ms N"
          by fastforce
        then show ?thesis
          using calculation(2) by presburger
      qed
    ultimately have "dpll\<^sub>W\<^sup>*\<^sup>* (toS S\<^sub>1' N) (toS Ms' N)" using IH[of "(S\<^sub>1, S\<^sub>2)" S\<^sub>1 S\<^sub>2] S step by simp

    moreover have "dpll\<^sub>W (toS Ms N) (toS S\<^sub>1 N)"
      by (metis DPLL_step_is_a_dpll\<^sub>W_step S \<open>(S\<^sub>1, S\<^sub>2) \<noteq> (Ms, N)\<close> prod.sel(2) snd_DPLL_step)
    ultimately have ?case by (metis (mono_tags, opaque_lifting) IH S \<open>(S\<^sub>1, S\<^sub>2) \<noteq> (Ms, N)\<close>
      \<open>DPLL_ci Ms N = DPLL_ci S\<^sub>1 N\<close> \<open>dpll\<^sub>W_all_inv (toS Ms N)\<close> converse_rtranclp_into_rtranclp
      local.step)
  }
  ultimately show ?case by blast
qed

lemma dpll\<^sub>W_all_inv_dpll\<^sub>W_tranclp_irrefl:
  assumes "dpll\<^sub>W_all_inv (Ms, N)"
  and "dpll\<^sub>W\<^sup>+\<^sup>+ (Ms, N) (Ms, N)"
  shows "False"
proof -
  have 1: "wf {(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W\<^sup>+\<^sup>+ S S'}" using wf_dpll\<^sub>W_tranclp by auto
  have "((Ms, N), (Ms, N)) \<in> {(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W\<^sup>+\<^sup>+ S S'}" using assms by auto
  then show False using wf_not_refl[OF 1] by blast
qed

lemma DPLL_ci_final_state:
  assumes step: "DPLL_ci Ms N = (Ms, N)"
  and inv: "dpll\<^sub>W_all_inv (toS Ms N)"
  shows "conclusive_dpll\<^sub>W_state (toS Ms N)"
proof -
  have st: "dpll\<^sub>W\<^sup>*\<^sup>* (toS Ms N) (toS Ms N)" using DPLL_ci_dpll\<^sub>W_rtranclp[OF step] .
  have "DPLL_step (Ms, N) = (Ms, N)"
    proof (rule ccontr)
      obtain Ms' N' where Ms'N: "(Ms', N') = DPLL_step (Ms, N)"
        by (cases "DPLL_step (Ms, N)") auto
      assume "\<not> ?thesis"
      then have "DPLL_ci Ms' N = (Ms, N)" using step inv st Ms'N[symmetric] by fastforce
      then have "dpll\<^sub>W\<^sup>+\<^sup>+ (toS Ms N) (toS Ms N)"
        by (metis DPLL_ci_dpll\<^sub>W_rtranclp DPLL_step_is_a_dpll\<^sub>W_step Ms'N \<open>DPLL_step (Ms, N) \<noteq> (Ms, N)\<close>
          prod.sel(2) rtranclp_into_tranclp2 snd_DPLL_step)
      then show False using dpll\<^sub>W_all_inv_dpll\<^sub>W_tranclp_irrefl inv by auto
    qed
  then show ?thesis using DPLL_step_stuck_final_state[of Ms N] by simp
qed

lemma DPLL_step_obtains:
  obtains Ms' where "(Ms', N) = DPLL_step (Ms, N)"
  unfolding DPLL_step_def by (metis (no_types, lifting) DPLL_step_def prod.collapse snd_DPLL_step)

lemma DPLL_ci_obtains:
  obtains Ms' where "(Ms', N) = DPLL_ci Ms N"
proof (induct rule: DPLL_ci.induct)
  case (1 Ms N) note IH = this(1) and that = this(2)
  obtain S where SN: "(S, N) = DPLL_step (Ms, N)" using DPLL_step_obtains by metis
  { assume "\<not> dpll\<^sub>W_all_inv (toS Ms N)"
    then have ?case using that by auto
  }
  moreover {
    assume n: "(S, N) \<noteq> (Ms, N)"
    and inv: "dpll\<^sub>W_all_inv (toS Ms N)"
    have "\<exists>ms. DPLL_step (Ms, N) = (ms, N)"
      by (metis \<open>\<And>thesisa. (\<And>S. (S, N) = DPLL_step (Ms, N) \<Longrightarrow> thesisa) \<Longrightarrow> thesisa\<close>)
    then have ?thesis
      using IH that by fastforce
  }
  moreover {
    assume n: "(S, N) = (Ms, N)"
    then have ?case using SN that by fastforce
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
  { assume "\<not>dpll\<^sub>W_all_inv (toS Ms N)"
    then have ?case using step by auto
  }
  moreover {
    assume "dpll\<^sub>W_all_inv (toS Ms N)"
    and "(S\<^sub>1, N) = (Ms, N)"
    then have ?case using S step by auto
  }
  moreover
  { assume inv: "dpll\<^sub>W_all_inv (toS Ms N)"
    assume n: "(S\<^sub>1, N) \<noteq> (Ms, N)"
    obtain S\<^sub>1' where SS: "(S\<^sub>1', N) = DPLL_ci S\<^sub>1 N" using DPLL_ci_obtains by blast
    moreover have "DPLL_ci Ms N = DPLL_ci S\<^sub>1 N"
      proof -
        have "(case (S\<^sub>1, N) of (ms, lss) \<Rightarrow> if (ms, lss) = (Ms, N) then (Ms, N) else DPLL_ci ms N)
 = DPLL_ci Ms N"
          using S DPLL_ci.simps[of Ms N] calculation inv by presburger
        then have "(if (S\<^sub>1, N) = (Ms, N) then (Ms, N) else DPLL_ci S\<^sub>1 N) = DPLL_ci Ms N"
          by fastforce
        then show ?thesis
          using calculation n by presburger
      qed
    moreover
      have "DPLL_ci S\<^sub>1' N = (S\<^sub>1', N)" using step IH[OF _ _ S n SS[symmetric]] inv by blast
    ultimately have ?case using step by fastforce
  }
  ultimately show ?case by blast
qed


lemma DPLL_part_dpll\<^sub>W_all_inv_final:
  fixes M Ms':: "(int, unit) ann_lits" and
    N :: "int literal list list"
  assumes inv: "dpll\<^sub>W_all_inv (Ms, mset (map mset N))"
  and MsN: "DPLL_part Ms N = (Ms', N)"
  shows "conclusive_dpll\<^sub>W_state (toS Ms' N) \<and> dpll\<^sub>W\<^sup>*\<^sup>* (toS Ms N) (toS Ms' N)"
proof -
  have 2: "DPLL_ci Ms N = DPLL_part Ms N" using inv dpll\<^sub>W_all_inv_implieS_2_eq3_and_dom by blast
  then have star: "dpll\<^sub>W\<^sup>*\<^sup>* (toS Ms N) (toS Ms' N)" unfolding MsN using DPLL_ci_dpll\<^sub>W_rtranclp by blast
  then have inv': "dpll\<^sub>W_all_inv (toS Ms' N)" using inv rtranclp_dpll\<^sub>W_all_inv by blast
  show ?thesis using star DPLL_ci_final_state[OF DPLL_ci_no_more_step inv'] 2 unfolding MsN by blast
qed

paragraph \<open>Embedding the invariant into the type\<close>
paragraph \<open>Defining the type\<close>
typedef dpll\<^sub>W_state =
    "{(M::(int, unit) ann_lits, N::int literal list list).
        dpll\<^sub>W_all_inv (toS M N)}"
  morphisms rough_state_of state_of
proof
    show "([],[]) \<in> {(M, N). dpll\<^sub>W_all_inv (toS M N)}" by (auto simp add: dpll\<^sub>W_all_inv_def)
qed

lemma
  "DPLL_part_dom ([], N)"
  using dpll\<^sub>W_all_inv_implieS_2_eq3_and_dom[of "[]" N] by (simp add: dpll\<^sub>W_all_inv_def)

paragraph \<open>Some type classes\<close>
instantiation dpll\<^sub>W_state :: equal
begin
definition equal_dpll\<^sub>W_state :: "dpll\<^sub>W_state \<Rightarrow> dpll\<^sub>W_state \<Rightarrow> bool" where
 "equal_dpll\<^sub>W_state S S' = (rough_state_of S = rough_state_of S')"
instance
  by standard (simp add: rough_state_of_inject equal_dpll\<^sub>W_state_def)
end

paragraph \<open>DPLL\<close>
definition DPLL_step' :: "dpll\<^sub>W_state \<Rightarrow> dpll\<^sub>W_state" where
  "DPLL_step' S = state_of (DPLL_step (rough_state_of S))"

declare rough_state_of_inverse[simp]

lemma DPLL_step_dpll\<^sub>W_conc_inv:
  "DPLL_step (rough_state_of S) \<in> {(M, N). dpll\<^sub>W_all_inv (toS M N)}"
proof -
  obtain M N where
    S: \<open>rough_state_of S = (M, N)\<close>
    by (cases \<open>rough_state_of S\<close>)
  obtain M' N' where
    S': \<open>DPLL_step (rough_state_of S) = (M', N')\<close>
    by (cases \<open>DPLL_step (rough_state_of S)\<close>)
  have \<open>dpll\<^sub>W\<^sup>*\<^sup>*  (toS M N) (toS M' N')\<close>
    by (metis DPLL_step_is_a_dpll\<^sub>W_step S S' fst_conv r_into_rtranclp rtranclp.rtrancl_refl snd_conv)
  then show ?thesis
    using rough_state_of[of S] unfolding S' unfolding S by (auto intro: rtranclp_dpll\<^sub>W_all_inv)
qed

lemma rough_state_of_DPLL_step'_DPLL_step[simp]:
  "rough_state_of (DPLL_step' S) = DPLL_step (rough_state_of S)"
  using DPLL_step_dpll\<^sub>W_conc_inv DPLL_step'_def state_of_inverse by auto

function DPLL_tot:: "dpll\<^sub>W_state \<Rightarrow> dpll\<^sub>W_state" where
"DPLL_tot S =
  (let S' = DPLL_step' S in
   if S' = S then S else DPLL_tot S')"
  by fast+
termination
proof (relation "{(T', T).
     (rough_state_of T', rough_state_of T)
        \<in> {(S', S). (toS' S', toS' S)
              \<in> {(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W S S'}}}")
  show "wf {(b, a).
          (rough_state_of b, rough_state_of a)
            \<in> {(b, a). (toS' b, toS' a)
              \<in> {(b, a). dpll\<^sub>W_all_inv a \<and> dpll\<^sub>W a b}}}"
    using wf_if_measure_f[OF wf_if_measure_f[OF wf_dpll\<^sub>W, of "toS'"], of rough_state_of] .
next
  fix S x
  assume x: "x = DPLL_step' S"
  and "x \<noteq> S"
  have "dpll\<^sub>W_all_inv (case rough_state_of S of (Ms, N) \<Rightarrow> (Ms, mset (map mset N)))"
    by (metis (no_types, lifting) case_prodE mem_Collect_eq old.prod.case rough_state_of)
  moreover have "dpll\<^sub>W (case rough_state_of S of (Ms, N) \<Rightarrow> (Ms, mset (map mset N)))
                      (case rough_state_of (DPLL_step' S) of (Ms, N) \<Rightarrow> (Ms, mset (map mset N)))"
    proof -
      obtain Ms N where Ms: "(Ms, N) = rough_state_of S" by (cases "rough_state_of S") auto
      have "dpll\<^sub>W_all_inv (toS' (Ms, N))" using calculation unfolding Ms by blast
      moreover obtain Ms' N' where Ms': "(Ms', N') = rough_state_of (DPLL_step' S)"
        by (cases "rough_state_of (DPLL_step' S)") auto
      ultimately have "dpll\<^sub>W_all_inv (toS' (Ms', N'))" unfolding Ms'
        by (metis (no_types, lifting) case_prod_unfold mem_Collect_eq rough_state_of)

      have "dpll\<^sub>W (toS Ms N) (toS Ms' N')"
        apply (rule DPLL_step_is_a_dpll\<^sub>W_step[of Ms' N' Ms N])
        unfolding Ms Ms' using \<open>x \<noteq> S\<close> rough_state_of_inject x by fastforce+
      then show ?thesis unfolding Ms[symmetric] Ms'[symmetric] by auto
    qed
  ultimately show "(x, S) \<in> {(T', T). (rough_state_of T', rough_state_of T)
    \<in> {(S', S). (toS' S', toS' S) \<in> {(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W S S'}}}"
    by (auto simp add: x)
qed

lemma [code]:
"DPLL_tot S =
  (let S' = DPLL_step' S in
   if S' = S then S else DPLL_tot S')" by auto

lemma DPLL_tot_DPLL_step_DPLL_tot[simp]: "DPLL_tot (DPLL_step' S) = DPLL_tot S"
  apply (cases "DPLL_step' S = S")
  apply simp
  unfolding DPLL_tot.simps[of S] by (simp del: DPLL_tot.simps)

lemma DOPLL_step'_DPLL_tot[simp]:
  "DPLL_step' (DPLL_tot S) = DPLL_tot S"
  by (rule DPLL_tot.induct[of "\<lambda>S. DPLL_step' (DPLL_tot S) = DPLL_tot S" S])
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
  shows "conclusive_dpll\<^sub>W_state (toS' (rough_state_of S))"
proof -
  have "DPLL_step' S = S" using assms[symmetric] DOPLL_step'_DPLL_tot by metis
  then have "DPLL_step (rough_state_of S) = (rough_state_of S)"
    unfolding DPLL_step'_def using DPLL_step_dpll\<^sub>W_conc_inv rough_state_of_inverse
    by (metis rough_state_of_DPLL_step'_DPLL_step)
  then show ?thesis
    by (metis (mono_tags, lifting) DPLL_step_stuck_final_state old.prod.exhaust split_conv)
qed

lemma DPLL_tot_star:
  assumes "rough_state_of (DPLL_tot S) = S'"
  shows "dpll\<^sub>W\<^sup>*\<^sup>* (toS' (rough_state_of S)) (toS' S')"
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
      apply (cases "DPLL_step' S = S")
        using S apply blast
      by (smt "1.IH" "1.prems" DPLL_step_is_a_dpll\<^sub>W_step DPLL_tot.simps case_prodE2
        rough_state_of_DPLL_step'_DPLL_step rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl
        rtranclp_idemp split_conv)
  }
  ultimately show ?case by auto
qed

lemma rough_state_of_rough_state_of_Nil[simp]:
  "rough_state_of (state_of ([], N)) = ([], N)"
  apply (rule DPLL_W_Implementation.dpll\<^sub>W_state.state_of_inverse)
  unfolding dpll\<^sub>W_all_inv_def by auto

text \<open>Theorem of correctness\<close>
lemma DPLL_tot_correct:
  assumes "rough_state_of (DPLL_tot (state_of (([], N)))) = (M, N')"
  and "(M', N'') = toS' (M, N')"
  shows "M' \<Turnstile>asm N'' \<longleftrightarrow> satisfiable (set_mset N'')"
proof -
  have "dpll\<^sub>W\<^sup>*\<^sup>* (toS' ([], N)) (toS' (M, N'))" using DPLL_tot_star[OF assms(1)] by auto
  moreover have "conclusive_dpll\<^sub>W_state (toS' (M, N'))"
    using DPLL_tot_final_state by (metis (mono_tags, lifting) DOPLL_step'_DPLL_tot DPLL_tot.simps
      assms(1))
  ultimately show ?thesis using dpll\<^sub>W_conclusive_state_correct by (smt DPLL_ci.simps
    DPLL_ci_dpll\<^sub>W_rtranclp assms(2) dpll\<^sub>W_all_inv_def prod.case prod.sel(1) prod.sel(2)
    rtranclp_dpll\<^sub>W_inv(3) rtranclp_dpll\<^sub>W_inv_starting_from_0)
qed


subsubsection \<open>Code export\<close>

paragraph \<open>A conversion to @{typ dpll\<^sub>W_state}\<close>
definition Con :: "(int, unit) ann_lits \<times> int literal list list
                     \<Rightarrow> dpll\<^sub>W_state" where
  "Con xs = state_of (if dpll\<^sub>W_all_inv (toS (fst xs) (snd xs)) then xs else ([], []))"
lemma [code abstype]:
  "Con (rough_state_of S) = S"
  using rough_state_of[of S] unfolding Con_def by auto

  declare rough_state_of_DPLL_step'_DPLL_step[code abstract]

lemma Con_DPLL_step_rough_state_of_state_of[simp]:
  "Con (DPLL_step (rough_state_of s)) = state_of (DPLL_step (rough_state_of s))"
  unfolding Con_def by (metis (mono_tags, lifting) DPLL_step_dpll\<^sub>W_conc_inv mem_Collect_eq
    prod.case_eq_if)

text \<open>A slightly different version of @{term DPLL_tot} where the returned boolean indicates the
  result.\<close>
definition DPLL_tot_rep where
"DPLL_tot_rep S =
  (let (M, N) = (rough_state_of (DPLL_tot S)) in (\<forall>A \<in> set N. (\<exists>a\<in>set A. a \<in> lits_of_l M), M))"

text \<open>One version of the generated SML code is here, but not included in the generated document.
  The only differences are:
  \<^item> export @{typ "'a literal"} from the SML Module \<open>Clausal_Logic\<close>;
  \<^item> export the constructor @{term Con} from \<open>DPLL_W_Implementation\<close>;
  \<^item> export the @{term int} constructor from \<open>Arith\<close>.

  All these allows to test on the code on some examples.
  \<close>

(*<*)
export_code DPLL_tot_rep in SML

ML \<open>
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
  val list_all : ('a -> bool) -> 'a list -> bool
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

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

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
  datatype int = Int_of_integer of IntInf.int
  val equal_int : int HOL.equal
end = struct

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

val equal_int = {equal = equal_inta} : int HOL.equal;

end; (*struct Arith*)

structure Product_Type : sig
  val equal_unit : unit HOL.equal
  val apfst : ('a -> 'b) -> 'a * 'c -> 'b * 'c
  val equal_prod : 'a HOL.equal -> 'b HOL.equal -> 'a * 'b -> 'a * 'b -> bool
end = struct

fun equal_unita u v = true;

val equal_unit = {equal = equal_unita} : unit HOL.equal;

fun apfst f (x, y) = (f x, y);

fun equal_prod A_ B_ (x1, x2) (y1, y2) =
  HOL.eq A_ x1 y1 andalso HOL.eq B_ x2 y2;

end; (*struct Product_Type*)

structure Clausal_Logic : sig
  datatype 'a literal = Pos of 'a | Neg of 'a
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

structure Partial_Annotated_Herbrand_Interpretation : sig
  datatype ('a, 'b) ann_lit = Decided of 'a Clausal_Logic.literal |
    Propagated of 'a Clausal_Logic.literal * 'b
  val equal_ann_lit : 'a HOL.equal -> 'b HOL.equal -> ('a, 'b) ann_lit HOL.equal
  val lit_of : ('a, 'b) ann_lit -> 'a Clausal_Logic.literal
  val lits_of : ('a, 'b) ann_lit Set.set -> 'a Clausal_Logic.literal Set.set
  val backtrack_split :
    ('a, 'b) ann_lit list -> ('a, 'b) ann_lit list * ('a, 'b) ann_lit list
end = struct

datatype ('a, 'b) ann_lit = Decided of 'a Clausal_Logic.literal |
  Propagated of 'a Clausal_Logic.literal * 'b;

fun equal_ann_lita A_ B_ (Decided x1) (Propagated (x21, x22)) = false
  | equal_ann_lita A_ B_ (Propagated (x21, x22)) (Decided x1) = false
  | equal_ann_lita A_ B_ (Propagated (x21, x22)) (Propagated (y21, y22)) =
    Clausal_Logic.equal_literala A_ x21 y21 andalso HOL.eq B_ x22 y22
  | equal_ann_lita A_ B_ (Decided x1) (Decided y1) =
    Clausal_Logic.equal_literala A_ x1 y1;

fun equal_ann_lit A_ B_ = {equal = equal_ann_lita A_ B_} :
  ('a, 'b) ann_lit HOL.equal;

fun lit_of (Decided x1) = x1
  | lit_of (Propagated (x21, x22)) = x21;

fun lits_of ls = Set.image lit_of ls;

fun backtrack_split [] = ([], [])
  | backtrack_split (Propagated (l, p) :: mlits) =
    Product_Type.apfst (fn a => Propagated (l, p) :: a) (backtrack_split mlits)
  | backtrack_split (Decided l :: mlits) = ([], Decided l :: mlits);

end; (*struct Partial_Annotated_Herbrand_Interpretation*)

structure DPLL_CDCL_W_Implementation : sig
  val find_first_unused_var :
    'a HOL.equal ->
      ('a Clausal_Logic.literal list) list ->
        'a Clausal_Logic.literal Set.set -> 'a Clausal_Logic.literal option
  val find_first_unit_clause :
    'a HOL.equal ->
      ('a Clausal_Logic.literal list) list ->
        ('a, 'b) Partial_Annotated_Herbrand_Interpretation.ann_lit list ->
          ('a Clausal_Logic.literal * 'a Clausal_Logic.literal list) option
end = struct

fun is_unit_clause_code A_ l m =
  (case List.filter
          (fn a =>
            not (Set.member A_ (Clausal_Logic.atm_of a)
                  (Set.image Clausal_Logic.atm_of
                    (Partial_Annotated_Herbrand_Interpretation.lits_of (Set.Set m)))))
          l
    of [] => NONE
    | [a] =>
      (if List.list_all
            (fn c =>
              Set.member (Clausal_Logic.equal_literal A_)
                (Clausal_Logic.uminus_literal c)
                (Partial_Annotated_Herbrand_Interpretation.lits_of (Set.Set m)))
            (List.remove1 (Clausal_Logic.equal_literal A_) a l)
        then SOME a else NONE)
    | _ :: _ :: _ => NONE);

fun is_unit_clause A_ l m = is_unit_clause_code A_ l m;

fun find_first_unused_var A_ (a :: l) m =
  (case List.find
          (fn lit =>
            not (Set.member (Clausal_Logic.equal_literal A_) lit m) andalso
              not (Set.member (Clausal_Logic.equal_literal A_)
                    (Clausal_Logic.uminus_literal lit) m))
          a
    of NONE => find_first_unused_var A_ l m | SOME aa => SOME aa)
  | find_first_unused_var A_ [] uu = NONE;

fun find_first_unit_clause A_ (a :: l) m =
  (case is_unit_clause A_ a m of NONE => find_first_unit_clause A_ l m
    | SOME la => SOME (la, a))
  | find_first_unit_clause A_ [] uu = NONE;

end; (*struct DPLL_CDCL_W_Implementation*)

structure DPLL_W_Implementation : sig
  datatype dpll_W_state =
    Con of
      ((Arith.int, unit) Partial_Annotated_Herbrand_Interpretation.ann_lit list *
        (Arith.int Clausal_Logic.literal list) list)
  val dPLL_tot_rep :
    dpll_W_state ->
      bool * (Arith.int, unit) Partial_Annotated_Herbrand_Interpretation.ann_lit list
end = struct

datatype dpll_W_state =
  Con of
    ((Arith.int, unit) Partial_Annotated_Herbrand_Interpretation.ann_lit list *
      (Arith.int Clausal_Logic.literal list) list);

fun rough_state_of (Con x) = x;

fun equal_dpll_W_state sa s =
  Product_Type.equal_prod
    (List.equal_list
      (Partial_Annotated_Herbrand_Interpretation.equal_ann_lit Arith.equal_int
        Product_Type.equal_unit))
    (List.equal_list
      (List.equal_list (Clausal_Logic.equal_literal Arith.equal_int)))
    (rough_state_of sa) (rough_state_of s);

fun dPLL_step x =
  (fn (ms, n) =>
    (case DPLL_CDCL_W_Implementation.find_first_unit_clause Arith.equal_int n ms
      of NONE =>
        (if List.list_ex
              (List.list_all
                (fn c =>
                  Set.member (Clausal_Logic.equal_literal Arith.equal_int)
                    (Clausal_Logic.uminus_literal c)
                    (Partial_Annotated_Herbrand_Interpretation.lits_of (Set.Set ms))))
              n
          then (case Partial_Annotated_Herbrand_Interpretation.backtrack_split ms
                 of (_, []) => (ms, n)
                 | (_, l :: m) =>
                   (Partial_Annotated_Herbrand_Interpretation.Propagated
                      (Clausal_Logic.uminus_literal
                         (Partial_Annotated_Herbrand_Interpretation.lit_of l),
                        ()) ::
                      m,
                     n))
          else (case DPLL_CDCL_W_Implementation.find_first_unused_var
                       Arith.equal_int n
                       (Partial_Annotated_Herbrand_Interpretation.lits_of (Set.Set ms))
                 of NONE => (ms, n)
                 | SOME a =>
                   (Partial_Annotated_Herbrand_Interpretation.Decided a :: ms, n)))
      | SOME (l, _) =>
        (Partial_Annotated_Herbrand_Interpretation.Propagated (l, ()) :: ms, n)))
    x;

fun dPLL_stepa s = Con (dPLL_step (rough_state_of s));

fun dPLL_tot s = let
                   val sa = dPLL_stepa s;
                 in
                   (if equal_dpll_W_state sa s then s else dPLL_tot sa)
                 end;

fun dPLL_tot_rep s =
  let
    val (m, n) = rough_state_of (dPLL_tot s);
  in
    (List.list_all
       (List.list_ex
         (fn a =>
           Set.member (Clausal_Logic.equal_literal Arith.equal_int) a
             (Partial_Annotated_Herbrand_Interpretation.lits_of (Set.Set m))))
       n,
      m)
  end;

end; (*struct DPLL_W_Implementation*)
\<close>

ML \<open>
open Clausal_Logic;
open DPLL_W_Implementation;
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
 DPLL_W_Implementation.dPLL_tot_rep (Con ([], N))

end
\<close>
ML \<open>
open Clausal_Logic;
open DPLL_W_Implementation;
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
 DPLL_W_Implementation.dPLL_tot_rep (Con ([], N))
end
\<close>

ML \<open>
open Clausal_Logic;
open DPLL_W_Implementation;
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
 DPLL_W_Implementation.dPLL_tot_rep (Con ([], N))
end
\<close>
declare[[ML_print_depth=100]]
ML \<open>
open Clausal_Logic;
open DPLL_W_Implementation;
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
 DPLL_W_Implementation.dPLL_tot_rep (Con ([], N))
end
\<close>

(*>*)
end
