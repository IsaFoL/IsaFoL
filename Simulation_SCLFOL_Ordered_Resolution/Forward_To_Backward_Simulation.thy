theory Forward_To_Backward_Simulation
  imports
    Main
    "VeriComp.Well_founded"
begin

inductive match_bisim for \<R>\<^sub>1 \<F>\<^sub>1 \<R>\<^sub>2 match order where
  bisim_final: "\<F>\<^sub>1 s1 \<Longrightarrow> match i s1 s2 \<Longrightarrow> n\<^sub>2 = 0 \<Longrightarrow>
    match_bisim \<R>\<^sub>1 \<F>\<^sub>1 \<R>\<^sub>2 match order (i, n\<^sub>2) s1 s2" |

  bisim_steps: "(\<R>\<^sub>1 ^^ Suc m) s1 s1' \<Longrightarrow> match i s1 s2\<^sub>0 \<Longrightarrow>
    (\<forall>k < m. \<forall>s1\<^sub>k s1\<^sub>k\<^sub>1. (\<R>\<^sub>1 ^^ k) s1 s1\<^sub>k \<longrightarrow> \<R>\<^sub>1 s1\<^sub>k s1\<^sub>k\<^sub>1 \<longrightarrow>
      (\<exists>i\<^sub>k i\<^sub>k\<^sub>1. match i\<^sub>k s1\<^sub>k s2\<^sub>0 \<and> match i\<^sub>k\<^sub>1 s1\<^sub>k\<^sub>1 s2\<^sub>0 \<and> order i\<^sub>k\<^sub>1 i\<^sub>k)) \<Longrightarrow>
    (\<R>\<^sub>2 ^^ n\<^sub>1) s2\<^sub>0 s2 \<Longrightarrow> (\<R>\<^sub>2 ^^ Suc n\<^sub>2) s2 s2' \<Longrightarrow> match i' s1' s2' \<Longrightarrow>
    match_bisim \<R>\<^sub>1 \<F>\<^sub>1 \<R>\<^sub>2 match order (i, n\<^sub>2) s1 s2"

definition simulation where
  "simulation \<R>\<^sub>1 \<R>\<^sub>2 match order \<longleftrightarrow>
    (\<forall>i s1 s2 s1'. match i s1 s2 \<longrightarrow> \<R>\<^sub>1 s1 s1' \<longrightarrow>
      (\<exists>s2' i'. \<R>\<^sub>2\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1' s2 \<and> order i' i))"

definition safe_state where
  "safe_state \<R> \<F> s \<longleftrightarrow> (\<forall>s'. \<R>\<^sup>*\<^sup>* s s' \<longrightarrow> \<F> s' \<or> (\<exists>s''. \<R> s' s''))"

lemma step_preserves_safe_state:
  "\<R> s s' \<Longrightarrow> safe_state \<R> \<F> s \<Longrightarrow> safe_state \<R> \<F> s'"
  by (simp add: converse_rtranclp_into_rtranclp safe_state_def)

lemma rtranclp_step_preserves_safe_state:
  "\<R>\<^sup>*\<^sup>* s s' \<Longrightarrow> safe_state \<R> \<F> s \<Longrightarrow> safe_state \<R> \<F> s'"
  by (simp add: rtranclp_induct step_preserves_safe_state)

lemma tranclp_step_preserves_safe_state:
  "\<R>\<^sup>+\<^sup>+ s s' \<Longrightarrow> safe_state \<R> \<F> s \<Longrightarrow> safe_state \<R> \<F> s'"
  by (simp add: step_preserves_safe_state tranclp_induct)

lemma safe_state_if_all_states_safe:
  assumes "\<And>s. \<F> s \<or> (\<exists>s'. \<R> s s')"
  shows "safe_state \<R> \<F> s"
  using assms by (simp add: safe_state_def)

theorem
  fixes
    step1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool" and
    step2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool" and
    match :: "'i \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool" and
    order :: "'i \<Rightarrow> 'i \<Rightarrow> bool"
  assumes
    "right_unique step1" and
    "right_unique step2" and
    final1_stuck: "\<And>s1. final1 s1 \<Longrightarrow> \<nexists>s1'. step1 s1 s1'" and
    final2_stuck: "\<And>s2. final2 s2 \<Longrightarrow> \<nexists>s2'. step2 s2 s2'" and
    Uniq_match_index: "\<forall>s1 s2. \<exists>\<^sub>\<le>\<^sub>1i. match i s1 s2" and
    matching_states_agree_on_final:
      "\<And>i s1 s2. match i s1 s2 \<Longrightarrow> final1 s1 \<longleftrightarrow> final2 s2" and
    matching_states_are_safe:
      "\<And>i s1 s2. match i s1 s2 \<Longrightarrow> safe_state step1 final1 s1 \<and> safe_state step2 final2 s2" and
    order_well_founded: "wfP order" and
    sim: "simulation step1 step2 match order"
  obtains
    MATCH :: "'i \<times> nat \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool" and
    ORDER :: "'i \<times> nat \<Rightarrow> 'i \<times> nat \<Rightarrow> bool"
  where
    "\<And>i s1 s2. match i s1 s2 \<Longrightarrow> (\<exists>j. MATCH j s1 s2)"
    "\<And>j s1 s2. MATCH j s1 s2 \<Longrightarrow> final1 s1 \<longleftrightarrow> final2 s2" and
    "\<And>j s1 s2. MATCH j s1 s2 \<Longrightarrow> safe_state step1 final1 s1 \<and> safe_state step2 final2 s2" and
    "wfP ORDER" and
    "simulation step1 step2 (\<lambda>i s1 s2. MATCH i s1 s2) ORDER" and
    "simulation step2 step1 (\<lambda>i s2 s1. MATCH i s1 s2) ORDER"
proof -
  from \<open>right_unique step1\<close> have determ1: "\<And>s1. \<exists>\<^sub>\<le>\<^sub>1s1'. step1 s1 s1'"
    by (simp add: right_unique_iff)

  from \<open>right_unique step2\<close> have determ2: "\<And>s2. \<exists>\<^sub>\<le>\<^sub>1s2'. step2 s2 s2'"
    by (simp add: right_unique_iff)

  define MATCH where
    "MATCH = match_bisim step1 final1 step2 match order"

  define ORDER :: "'i \<times> nat \<Rightarrow> 'i \<times> nat \<Rightarrow> bool" where
    "ORDER = lex_prodp order ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)"

  have MATCH_if_match: "\<And>i s1 s2. match i s1 s2 \<Longrightarrow> \<exists>j. MATCH j s1 s2"
  proof -
    fix i s1 s2
    assume "match i s1 s2"

    have "final1 s1 \<longleftrightarrow> final2 s2"
      using \<open>match i s1 s2\<close> matching_states_agree_on_final by metis
    moreover have "safe_state step1 final1 s1" and "safe_state step2 final2 s2"
      using \<open>match i s1 s2\<close> matching_states_are_safe by simp_all
    ultimately have "(final1 s1 \<and> final2 s2) \<or> (\<exists>s1' s2'. step1 s1 s1' \<and> step2 s2 s2')"
      by (metis rtranclp.rtrancl_refl safe_state_def)
    thus "\<exists>j. MATCH j s1 s2"
    proof (elim disjE conjE exE)
      show "final1 s1 \<Longrightarrow> final2 s2 \<Longrightarrow> \<exists>j. MATCH j s1 s2"
        by (metis MATCH_def \<open>match i s1 s2\<close> bisim_final)
    next
      fix s1' s2'
      assume "step1 s1 s1'" and "step2 s2 s2'"

      have "\<exists>m s1''. (step1 ^^ m) s1' s1'' \<and>
        (\<forall>k < m. \<forall>s1\<^sub>k s1\<^sub>k\<^sub>1. (step1 ^^ k) s1 s1\<^sub>k \<longrightarrow> step1 s1\<^sub>k s1\<^sub>k\<^sub>1 \<longrightarrow>
          (\<exists>i\<^sub>k i\<^sub>k\<^sub>1. match i\<^sub>k s1\<^sub>k s2 \<and> match i\<^sub>k\<^sub>1 s1\<^sub>k\<^sub>1 s2 \<and> order i\<^sub>k\<^sub>1 i\<^sub>k)) \<and>
        (\<exists>s2' i'. step2\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1'' s2')"
        using order_well_founded \<open>match i s1 s2\<close> \<open>step1 s1 s1'\<close>
      proof (induction i arbitrary: s1 s1' rule: wfP_induct_rule)
        case (less i)
        show ?case
          using sim[unfolded simulation_def, rule_format, OF \<open>match i s1 s2\<close> \<open>step1 s1 s1'\<close>]
        proof (elim disjE exE conjE)
          show "\<And>s2' i'. step2\<^sup>+\<^sup>+ s2 s2' \<Longrightarrow> match i' s1' s2' \<Longrightarrow> ?thesis"
            by force
        next
          fix i'
          assume "match i' s1' s2" and "order i' i"

          have "\<not> final2 s2"
            using \<open>step2 s2 s2'\<close> final2_stuck by metis

          hence "\<not> final1 s1'"
            using \<open>match i' s1' s2\<close> matching_states_agree_on_final by metis

          moreover have "safe_state step1 final1 s1'"
            using \<open>match i' s1' s2\<close> matching_states_are_safe by metis

          ultimately obtain s1'' where "step1 s1' s1''"
            by (metis rtranclp.rtrancl_refl safe_state_def)

          obtain m s1''' s2' i'' where
            "(step1 ^^ m) s1'' s1'''" and
            inbetween_match: "\<forall>k < m. \<forall>s1\<^sub>k s1\<^sub>k\<^sub>1. (step1 ^^ k) s1' s1\<^sub>k \<longrightarrow> step1 s1\<^sub>k s1\<^sub>k\<^sub>1 \<longrightarrow>
              (\<exists>i\<^sub>k i\<^sub>k\<^sub>1. match i\<^sub>k s1\<^sub>k s2 \<and> match i\<^sub>k\<^sub>1 s1\<^sub>k\<^sub>1 s2 \<and> order i\<^sub>k\<^sub>1 i\<^sub>k)" and
            "step2\<^sup>+\<^sup>+ s2 s2'" and
            "match i'' s1''' s2'"
            using less.IH[OF \<open>order i' i\<close> \<open>match i' s1' s2\<close> \<open>step1 s1' s1''\<close>] by metis

          show ?thesis
          proof (intro exI conjI)
            show "(step1 ^^ Suc m) s1' s1'''"
              using \<open>(step1 ^^ m) s1'' s1'''\<close> \<open>step1 s1' s1''\<close> by (metis relpowp_Suc_I2)
          next
            show "\<forall>k<Suc m. \<forall>s1\<^sub>k s1\<^sub>k\<^sub>1. (step1 ^^ k) s1 s1\<^sub>k \<longrightarrow> step1 s1\<^sub>k s1\<^sub>k\<^sub>1 \<longrightarrow>
              (\<exists>i\<^sub>k i\<^sub>k\<^sub>1. match i\<^sub>k s1\<^sub>k s2 \<and> match i\<^sub>k\<^sub>1 s1\<^sub>k\<^sub>1 s2 \<and> order i\<^sub>k\<^sub>1 i\<^sub>k)"
              using inbetween_match
              using \<open>step1 s1 s1'\<close> \<open>match i s1 s2\<close> \<open>match i' s1' s2\<close> \<open>order i' i\<close>
              by (smt (verit, best) Suc_less_eq Uniq_D determ1 relpowp_E2)
          next
            show "step2\<^sup>+\<^sup>+ s2 s2'"
              using \<open>step2\<^sup>+\<^sup>+ s2 s2'\<close> .
          next
            show "match i'' s1''' s2'"
              using \<open>match i'' s1''' s2'\<close> .
          qed
        qed
      qed
      then obtain m s1'' s2' i' where
        "(step1 ^^ m) s1' s1''" and
        inbetween_match: "\<forall>k < m. \<forall>s1\<^sub>k s1\<^sub>k\<^sub>1. (step1 ^^ k) s1 s1\<^sub>k \<longrightarrow> step1 s1\<^sub>k s1\<^sub>k\<^sub>1 \<longrightarrow>
          (\<exists>i\<^sub>k i\<^sub>k\<^sub>1. match i\<^sub>k s1\<^sub>k s2 \<and> match i\<^sub>k\<^sub>1 s1\<^sub>k\<^sub>1 s2 \<and> order i\<^sub>k\<^sub>1 i\<^sub>k)" and
        "step2\<^sup>+\<^sup>+ s2 s2'" and
        "match i' s1'' s2'"
        by metis

      obtain n where "(step2 ^^ Suc n) s2 s2'"
        using \<open>step2\<^sup>+\<^sup>+ s2 s2'\<close> by (metis Suc_pred tranclp_power)

      show "\<exists>j. MATCH j s1 s2"
      proof (intro exI)
        show "MATCH (i, n) s1 s2"
          unfolding MATCH_def
        proof (rule bisim_steps)
          show "(step1 ^^ Suc m) s1 s1''"
            using \<open>step1 s1 s1'\<close> \<open>(step1 ^^ m) s1' s1''\<close> by (metis relpowp_Suc_I2)
        next
          show "match i s1 s2"
            using \<open>match i s1 s2\<close> .
        next
          show "\<forall>k < m. \<forall>s1\<^sub>k s1\<^sub>k\<^sub>1. (step1 ^^ k) s1 s1\<^sub>k \<longrightarrow> step1 s1\<^sub>k s1\<^sub>k\<^sub>1 \<longrightarrow>
            (\<exists>i\<^sub>k i\<^sub>k\<^sub>1. match i\<^sub>k s1\<^sub>k s2 \<and> match i\<^sub>k\<^sub>1 s1\<^sub>k\<^sub>1 s2 \<and> order i\<^sub>k\<^sub>1 i\<^sub>k)"
            using inbetween_match .
        next
          show "(step2 ^^ 0) s2 s2"
            by simp
        next
          show "(step2 ^^ Suc n) s2 s2'"
            using \<open>(step2 ^^ Suc n) s2 s2'\<close> .
        next
          show "match i' s1'' s2'"
            using \<open>match i' s1'' s2'\<close> .
        qed
      qed
    qed
  qed

  show thesis
  proof (rule that)
    show "\<And>i s1 s2. match i s1 s2 \<Longrightarrow> \<exists>j. MATCH j s1 s2"
      using MATCH_if_match .
  next
    fix j :: "'i \<times> nat" and s1 :: 's1 and s2 :: 's2
    assume "MATCH j s1 s2"
    thus "final1 s1 \<longleftrightarrow> final2 s2"
      unfolding MATCH_def
    proof (cases step1 final1 step2 match order j s1 s2 rule: match_bisim.cases)
      case (bisim_final i n\<^sub>2)
      thus ?thesis
        using matching_states_agree_on_final by metis
    next
      case (bisim_steps m s1' i s2\<^sub>0 n\<^sub>1 n\<^sub>2 s2' i')
      have "\<not> final1 s1"
        by (metis final1_stuck local.bisim_steps(2) relpowp_Suc_D2)
      moreover have "\<not> final2 s2"
        by (metis final2_stuck local.bisim_steps(6) relpowp_Suc_D2)
      ultimately show ?thesis
        by argo
    qed
  next
    fix j :: "'i \<times> nat" and s1 :: 's1 and s2 :: 's2
    assume "MATCH j s1 s2"
    thus "safe_state step1 final1 s1 \<and> safe_state step2 final2 s2"
      unfolding MATCH_def
    proof (cases step1 final1 step2 match order j s1 s2 rule: match_bisim.cases)
      case (bisim_final i n\<^sub>2)
      thus ?thesis
        using matching_states_are_safe by metis
    next
      case (bisim_steps m s1' i s2\<^sub>0 n\<^sub>1 n\<^sub>2 s2' i')
      thus ?thesis
        by (metis matching_states_are_safe relpowp_imp_rtranclp rtranclp_step_preserves_safe_state)
    qed
  next
    show "wfP ORDER"
      unfolding ORDER_def
      using lex_prodp_wfP wfP_less order_well_founded by metis
  next
    show "simulation step1 step2 MATCH ORDER"
      unfolding simulation_def
    proof (intro allI impI)
      fix j :: "'i \<times> nat" and s1 s1' :: 's1 and s2 :: 's2
      assume "MATCH j s1 s2" and "step1 s1 s1'"
      hence "match_bisim step1 final1 step2 match order j s1 s2"
        unfolding MATCH_def by metis
      thus "(\<exists>s2' j'. step2\<^sup>+\<^sup>+ s2 s2' \<and> MATCH j' s1' s2') \<or> (\<exists>j'. MATCH j' s1' s2 \<and> ORDER j' j)"
      proof (cases step1 final1 step2 match order j s1 s2 rule: match_bisim.cases)
        case (bisim_final i n\<^sub>2)
        hence False
          using \<open>step1 s1 s1'\<close> final1_stuck by metis
        thus ?thesis ..
      next
        case (bisim_steps m s1'' i s2\<^sub>0 n\<^sub>1 n\<^sub>2 s2' i')

        have "(step1 ^^ m) s1' s1''"
          using \<open>step1 s1 s1'\<close> \<open>(step1 ^^ Suc m) s1 s1''\<close>
          by (metis Uniq_D determ1 relpowp_Suc_D2)

        show ?thesis
        proof (cases m)
          case 0
          hence "s1'' = s1'"
            using \<open>(step1 ^^ m) s1' s1''\<close> by simp

          have "step2\<^sup>+\<^sup>+ s2 s2'"
            using \<open>(step2 ^^ Suc n\<^sub>2) s2 s2'\<close> by (metis tranclp_power zero_less_Suc)

          moreover have "\<exists>j'. MATCH j' s1' s2'"
            using \<open>match i' s1'' s2'\<close> \<open>s1'' = s1'\<close> MATCH_if_match by metis

          ultimately show ?thesis
            by metis
        next
          case (Suc m')
          then obtain i\<^sub>k i\<^sub>k\<^sub>1 where
            "match i\<^sub>k s1 s2\<^sub>0" and "match i\<^sub>k\<^sub>1 s1' s2\<^sub>0" and "order i\<^sub>k\<^sub>1 i\<^sub>k"
            using \<open>\<forall>k<m. \<forall>s1\<^sub>k s1\<^sub>k\<^sub>1. (step1 ^^ k) s1 s1\<^sub>k \<longrightarrow> step1 s1\<^sub>k s1\<^sub>k\<^sub>1 \<longrightarrow>
              (\<exists>i\<^sub>k i\<^sub>k\<^sub>1. match i\<^sub>k s1\<^sub>k s2\<^sub>0 \<and> match i\<^sub>k\<^sub>1 s1\<^sub>k\<^sub>1 s2\<^sub>0 \<and> order i\<^sub>k\<^sub>1 i\<^sub>k)\<close>
            using \<open>step1 s1 s1'\<close>
            by fastforce

          define j' where
            "j' = (i\<^sub>k\<^sub>1, n\<^sub>2)"

          have "MATCH j' s1' s2"
            unfolding MATCH_def j'_def
          proof (rule match_bisim.bisim_steps)
            show "(step1 ^^ Suc m') s1' s1''"
              using \<open>(step1 ^^ m) s1' s1''\<close> \<open>m = Suc m'\<close> by argo
          next
            show "match i\<^sub>k\<^sub>1 s1' s2\<^sub>0"
              using \<open>match i\<^sub>k\<^sub>1 s1' s2\<^sub>0\<close> .
          next
            show "\<forall>k < m'. \<forall>s1\<^sub>k s1\<^sub>k\<^sub>1. (step1 ^^ k) s1' s1\<^sub>k \<longrightarrow> step1 s1\<^sub>k s1\<^sub>k\<^sub>1 \<longrightarrow>
              (\<exists>i\<^sub>k i\<^sub>k\<^sub>1. match i\<^sub>k s1\<^sub>k s2\<^sub>0 \<and> match i\<^sub>k\<^sub>1 s1\<^sub>k\<^sub>1 s2\<^sub>0 \<and> order i\<^sub>k\<^sub>1 i\<^sub>k)"
              by (metis Suc \<open>step1 s1 s1'\<close> local.bisim_steps(4) not_less_eq relpowp_Suc_I2)
          next
            show "(step2 ^^ n\<^sub>1) s2\<^sub>0 s2"
              using \<open>(step2 ^^ n\<^sub>1) s2\<^sub>0 s2\<close> .
          next
            show "(step2 ^^ Suc n\<^sub>2) s2 s2'"
              using \<open>(step2 ^^ Suc n\<^sub>2) s2 s2'\<close> .
          next
            show "match i' s1'' s2'"
              using \<open>match i' s1'' s2'\<close> .
          qed

          moreover have "ORDER j' j"
          proof -
            have "i\<^sub>k = i"
              using Uniq_match_index
              by (metis \<open>match i\<^sub>k s1 s2\<^sub>0\<close> local.bisim_steps(3) the1_equality')

            thus ?thesis
              unfolding ORDER_def j'_def \<open>j = (i, n\<^sub>2)\<close> prod.case
              using \<open>order i\<^sub>k\<^sub>1 i\<^sub>k\<close> by (simp add: lex_prodp_def)
          qed

          ultimately show ?thesis
            by metis
        qed
      qed
    qed
  next
    show "simulation step2 step1 (\<lambda>i s2 s1. MATCH i s1 s2) ORDER"
      unfolding simulation_def
    proof (intro allI impI)
      fix j :: "'i \<times> nat" and s1 :: 's1 and s2 s2' :: 's2
      assume "MATCH j s1 s2" and "step2 s2 s2'"
      hence "match_bisim step1 final1 step2 match order j s1 s2"
        unfolding MATCH_def by metis
      thus "(\<exists>s1' j'. step1\<^sup>+\<^sup>+ s1 s1' \<and> MATCH j' s1' s2') \<or> (\<exists>j'. MATCH j' s1 s2' \<and> ORDER j' j)"
      proof (cases step1 final1 step2 match order j s1 s2 rule: match_bisim.cases)
        case (bisim_final i n\<^sub>2)
        hence "final2 s2"
          using matching_states_agree_on_final by metis
        hence False
          using \<open>step2 s2 s2'\<close> final2_stuck by metis
        thus ?thesis ..
      next
        case (bisim_steps m s1' i s2\<^sub>0 n\<^sub>1 n\<^sub>2 s2'' i')
        show ?thesis
        proof (cases n\<^sub>2)
          case 0
          hence "s2'' = s2'"
            using \<open>step2 s2 s2'\<close> \<open>(step2 ^^ Suc n\<^sub>2) s2 s2''\<close>
            by (metis One_nat_def Uniq_D determ2 relpowp_1)

          have "step1\<^sup>+\<^sup>+ s1 s1'"
            using \<open>(step1 ^^ Suc m) s1 s1'\<close>
            by (metis less_Suc_eq_0_disj tranclp_power)

          moreover have "\<exists>j'. MATCH j' s1' s2'"
            using \<open>match i' s1' s2''\<close> \<open>s2'' = s2'\<close> MATCH_if_match by metis

          ultimately show ?thesis
            by metis
        next
          case (Suc n\<^sub>2')

          define j' where
            "j' = (i, n\<^sub>2')"

          have "MATCH j' s1 s2'"
            unfolding MATCH_def j'_def
          proof (rule match_bisim.bisim_steps)
            show "(step1 ^^ Suc m) s1 s1'"
              using \<open>(step1 ^^ Suc m) s1 s1'\<close> .
          next
            show "match i s1 s2\<^sub>0"
              using \<open>match i s1 s2\<^sub>0\<close> .
          next
            show "\<forall>k < m. \<forall>s1\<^sub>k s1\<^sub>k\<^sub>1. (step1 ^^ k) s1 s1\<^sub>k \<longrightarrow> step1 s1\<^sub>k s1\<^sub>k\<^sub>1 \<longrightarrow>
              (\<exists>i\<^sub>k i\<^sub>k\<^sub>1. match i\<^sub>k s1\<^sub>k s2\<^sub>0 \<and> match i\<^sub>k\<^sub>1 s1\<^sub>k\<^sub>1 s2\<^sub>0 \<and> order i\<^sub>k\<^sub>1 i\<^sub>k)"
              using \<open>\<forall>k < m. \<forall>s1\<^sub>k s1\<^sub>k\<^sub>1. (step1 ^^ k) s1 s1\<^sub>k \<longrightarrow> step1 s1\<^sub>k s1\<^sub>k\<^sub>1 \<longrightarrow>
                (\<exists>i\<^sub>k i\<^sub>k\<^sub>1. match i\<^sub>k s1\<^sub>k s2\<^sub>0 \<and> match i\<^sub>k\<^sub>1 s1\<^sub>k\<^sub>1 s2\<^sub>0 \<and> order i\<^sub>k\<^sub>1 i\<^sub>k)\<close> .
          next
            show "(step2 ^^ Suc n\<^sub>1) s2\<^sub>0 s2'"
              using \<open>(step2 ^^ n\<^sub>1) s2\<^sub>0 s2\<close> \<open>step2 s2 s2'\<close> by auto
          next
            show "(step2 ^^ Suc n\<^sub>2') s2' s2''"
              using \<open>step2 s2 s2'\<close> \<open>(step2 ^^ Suc n\<^sub>2) s2 s2''\<close>
              by (metis Suc Uniq_D determ2 relpowp_Suc_D2)
          next
            show "match i' s1' s2''"
              using \<open>match i' s1' s2''\<close> .
          qed

          moreover have "ORDER j' j"
            unfolding ORDER_def j'_def \<open>j = (i, n\<^sub>2)\<close> \<open>n\<^sub>2 = Suc n\<^sub>2'\<close>
            by (simp add: lex_prodp_def)

          ultimately show ?thesis
            by metis
        qed
      qed
    qed
  qed
qed

end