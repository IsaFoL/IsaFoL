theory CDCL_W_Restart
imports CDCL_W_Full
begin

chapter \<open>Extensions on Weidenbach's CDCL\<close>

text \<open>We here extend our calculus.\<close>

section \<open>Restarts\<close>

locale cdcl\<^sub>W_restart_restart =
  conflict_driven_clause_learning\<^sub>W
    state_eq
    state
    \<comment> \<open>functions for the state: \<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>get state:\<close>
    init_state
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'b" and
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and

    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" +
  fixes
    f :: "nat \<Rightarrow> nat"
  assumes
    f: "unbounded f"
begin

text \<open>The condition of the differences of cardinality has to be strict.
  Otherwise, you could be in a strange state, where nothing remains to do, but a restart is done.
  See the proof of well-foundedness.\<close>

inductive cdcl\<^sub>W_merge_with_restart where
restart_step:
  "(cdcl\<^sub>W_stgy^^(card (set_mset (learned_clss T)) - card (set_mset (learned_clss S)))) S T
  \<Longrightarrow> card (set_mset (learned_clss T)) - card (set_mset (learned_clss S)) > f n
  \<Longrightarrow> restart T U \<Longrightarrow> cdcl\<^sub>W_merge_with_restart (S, n) (U, Suc n)" |
restart_full: "full1 cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_merge_with_restart (S, n) (T, Suc n)"

lemma cdcl\<^sub>W_merge_with_restart_rtranclp_cdcl\<^sub>W_restart:
  "cdcl\<^sub>W_merge_with_restart S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* (fst S) (fst T)"
  by (induction rule: cdcl\<^sub>W_merge_with_restart.induct)
  (auto dest!: relpowp_imp_rtranclp rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart cdcl\<^sub>W_restart.rf
    cdcl\<^sub>W_rf.restart tranclp_into_rtranclp simp: full1_def)

lemma cdcl\<^sub>W_merge_with_restart_increasing_number:
  "cdcl\<^sub>W_merge_with_restart S T \<Longrightarrow> snd T = 1 + snd S"
  by (induction rule: cdcl\<^sub>W_merge_with_restart.induct) auto

lemma "full1 cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_merge_with_restart (S, n) (T, Suc n)"
  using restart_full by blast

lemma cdcl\<^sub>W_all_struct_inv_learned_clss_bound:
  assumes inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "set_mset (learned_clss S) \<subseteq> simple_clss (atms_of_mm (init_clss S))"
proof
  fix C
  assume C: "C \<in> set_mset (learned_clss S)"
  have "distinct_mset C"
    using C inv unfolding cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def distinct_mset_set_def
    by auto
  moreover have "\<not>tautology C"
    using C inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def by auto
  moreover
    have "atms_of C \<subseteq> atms_of_mm (learned_clss S)"
      using C by auto
    then have "atms_of C \<subseteq> atms_of_mm (init_clss S)"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def by force
  moreover have "finite (atms_of_mm (init_clss S))"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  ultimately show "C \<in> simple_clss (atms_of_mm (init_clss S))"
    using distinct_mset_not_tautology_implies_in_simple_clss simple_clss_mono
    by blast
qed

lemma cdcl\<^sub>W_merge_with_restart_init_clss:
  "cdcl\<^sub>W_merge_with_restart S T \<Longrightarrow> cdcl\<^sub>W_M_level_inv (fst S) \<Longrightarrow>
  init_clss (fst S) = init_clss (fst T)"
  using cdcl\<^sub>W_merge_with_restart_rtranclp_cdcl\<^sub>W_restart rtranclp_cdcl\<^sub>W_restart_init_clss by blast

lemma
  "wf {(T, S). cdcl\<^sub>W_all_struct_inv (fst S) \<and> cdcl\<^sub>W_merge_with_restart S T}"
proof (rule ccontr)
  assume "\<not> ?thesis"
    then obtain g where
    g: "\<And>i. cdcl\<^sub>W_merge_with_restart (g i) (g (Suc i))" and
    inv: "\<And>i. cdcl\<^sub>W_all_struct_inv (fst (g i))"
    unfolding wf_iff_no_infinite_down_chain by fast
  { fix i
    have "init_clss (fst (g i)) = init_clss (fst (g 0))"
      apply (induction i)
        apply simp
      using g inv unfolding cdcl\<^sub>W_all_struct_inv_def by (metis cdcl\<^sub>W_merge_with_restart_init_clss)
    } note init_g = this
  let ?S = "g 0"
  have "finite (atms_of_mm (init_clss (fst ?S)))"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have snd_g: "\<And>i. snd (g i) = i + snd (g 0)"
    apply (induct_tac i)
      apply simp
    by (metis Suc_eq_plus1_left add_Suc cdcl\<^sub>W_merge_with_restart_increasing_number g)
  then have snd_g_0: "\<And>i. i > 0 \<Longrightarrow> snd (g i) = i + snd (g 0)"
    by blast
  have unbounded_f_g: "unbounded (\<lambda>i. f (snd (g i)))"
    using f unfolding bounded_def by (metis add.commute f less_or_eq_imp_le snd_g
      not_bounded_nat_exists_larger not_le le_iff_add)

  obtain k where
    f_g_k: "f (snd (g k)) > card (simple_clss (atms_of_mm (init_clss (fst ?S))))" and
    "k > card (simple_clss (atms_of_mm (init_clss (fst ?S))))"
    using not_bounded_nat_exists_larger[OF unbounded_f_g] by blast
  text \<open>The following does not hold anymore with the non-strict version of
    cardinality in the definition.\<close>
  { fix i
    assume "no_step cdcl\<^sub>W_stgy (fst (g i))"
    with g[of i]
    have False
      proof (induction rule: cdcl\<^sub>W_merge_with_restart.induct)
        case (restart_step T S n) note H = this(1) and c = this(2) and n_s = this(4)
        obtain S' where "cdcl\<^sub>W_stgy S S'"
          using H c by (metis gr_implies_not0 relpowp_E2)
        then show False using n_s by auto
      next
        case (restart_full S T)
        then show False unfolding full1_def by (auto dest: tranclpD)
      qed
    } note H = this
  obtain m T where
    m: "m = card (set_mset (learned_clss T)) - card (set_mset (learned_clss (fst (g k))))" and
    "m > f (snd (g k))" and
    "restart T (fst (g (k+1)))" and
    cdcl\<^sub>W_stgy: "(cdcl\<^sub>W_stgy ^^ m) (fst (g k)) T"
    using g[of k] H[of "Suc k"] by (force simp: cdcl\<^sub>W_merge_with_restart.simps full1_def)
  have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (fst (g k)) T"
    using cdcl\<^sub>W_stgy relpowp_imp_rtranclp by metis
  then have "cdcl\<^sub>W_all_struct_inv T"
    using inv[of k] rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart
    by blast
  moreover have "card (set_mset (learned_clss T)) - card (set_mset (learned_clss (fst (g k))))
      > card (simple_clss (atms_of_mm (init_clss (fst ?S))))"
      unfolding m[symmetric] using \<open>m > f (snd (g k))\<close> f_g_k by linarith
    then have "card (set_mset (learned_clss T))
      > card (simple_clss (atms_of_mm (init_clss (fst ?S))))"
      by linarith
  moreover
    have "init_clss (fst (g k)) = init_clss T"
      using \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (fst (g k)) T\<close> rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart
      rtranclp_cdcl\<^sub>W_restart_init_clss inv unfolding cdcl\<^sub>W_all_struct_inv_def by blast
    then have "init_clss (fst ?S) = init_clss T"
      using init_g[of k] by auto
  ultimately show False
    using cdcl\<^sub>W_all_struct_inv_learned_clss_bound
    by (simp add: \<open>finite (atms_of_mm (init_clss (fst (g 0))))\<close> simple_clss_finite
      card_mono leD)
qed

lemma cdcl\<^sub>W_merge_with_restart_distinct_mset_clauses:
  assumes invR: "cdcl\<^sub>W_all_struct_inv (fst R)" and
  st: "cdcl\<^sub>W_merge_with_restart R S" and
  dist: "distinct_mset (clauses (fst R))" and
  R: \<open>no_smaller_propa (fst R)\<close>
  shows "distinct_mset (clauses (fst S))"
  using assms(2,1,3,4)
proof induction
  case (restart_full S T)
  then show ?case using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[of S T] unfolding full1_def
    by (auto dest: tranclp_into_rtranclp)
next
  case (restart_step T S n U)
  then have "distinct_mset (clauses T)"
    using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[of S T] unfolding full1_def
    by (auto dest: relpowp_imp_rtranclp)
  then show ?case using \<open>restart T U\<close>  unfolding clauses_def
    by (metis distinct_mset_union fstI restartE subset_mset.le_iff_add union_assoc)
qed

inductive cdcl\<^sub>W_restart_with_restart where
restart_step:
  "(cdcl\<^sub>W_stgy^^(card (set_mset (learned_clss T)) - card (set_mset (learned_clss S)))) S T \<Longrightarrow>
     card (set_mset (learned_clss T)) - card (set_mset (learned_clss S)) > f n \<Longrightarrow>
     restart T U \<Longrightarrow>
   cdcl\<^sub>W_restart_with_restart (S, n) (U, Suc n)" |
restart_full: "full1 cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_with_restart (S, n) (T, Suc n)"

lemma cdcl\<^sub>W_restart_with_restart_rtranclp_cdcl\<^sub>W_restart:
  "cdcl\<^sub>W_restart_with_restart S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* (fst S) (fst T)"
  apply (induction rule: cdcl\<^sub>W_restart_with_restart.induct)
  by (auto dest!: relpowp_imp_rtranclp tranclp_into_rtranclp cdcl\<^sub>W_restart.rf
     cdcl\<^sub>W_rf.restart rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart
    simp: full1_def)

lemma cdcl\<^sub>W_restart_with_restart_increasing_number:
  "cdcl\<^sub>W_restart_with_restart S T \<Longrightarrow> snd T = 1 + snd S"
  by (induction rule: cdcl\<^sub>W_restart_with_restart.induct) auto

lemma "full1 cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_with_restart (S, n) (T, Suc n)"
  using restart_full by blast

lemma cdcl\<^sub>W_restart_with_restart_init_clss:
  "cdcl\<^sub>W_restart_with_restart S T \<Longrightarrow>  cdcl\<^sub>W_M_level_inv (fst S) \<Longrightarrow> init_clss (fst S) = init_clss (fst T)"
  using cdcl\<^sub>W_restart_with_restart_rtranclp_cdcl\<^sub>W_restart rtranclp_cdcl\<^sub>W_restart_init_clss by blast

lemma
  "wf {(T, S). cdcl\<^sub>W_all_struct_inv (fst S) \<and> cdcl\<^sub>W_restart_with_restart S T}"
proof (rule ccontr)
  assume "\<not> ?thesis"
    then obtain g where
    g: "\<And>i. cdcl\<^sub>W_restart_with_restart (g i) (g (Suc i))" and
    inv: "\<And>i. cdcl\<^sub>W_all_struct_inv (fst (g i))"
    unfolding wf_iff_no_infinite_down_chain by fast
  { fix i
    have "init_clss (fst (g i)) = init_clss (fst (g 0))"
      apply (induction i)
        apply simp
      using g inv unfolding cdcl\<^sub>W_all_struct_inv_def by (metis cdcl\<^sub>W_restart_with_restart_init_clss)
    } note init_g = this
  let ?S = "g 0"
  have "finite (atms_of_mm (init_clss (fst ?S)))"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have snd_g: "\<And>i. snd (g i) = i + snd (g 0)"
    apply (induct_tac i)
      apply simp
    by (metis Suc_eq_plus1_left add_Suc cdcl\<^sub>W_restart_with_restart_increasing_number g)
  then have snd_g_0: "\<And>i. i > 0 \<Longrightarrow> snd (g i) = i + snd (g 0)"
    by blast
  have unbounded_f_g: "unbounded (\<lambda>i. f (snd (g i)))"
    using f unfolding bounded_def by (metis add.commute f less_or_eq_imp_le snd_g
      not_bounded_nat_exists_larger not_le le_iff_add)

  obtain k where
    f_g_k: "f (snd (g k)) > card (simple_clss (atms_of_mm (init_clss (fst ?S))))" and
    "k > card (simple_clss (atms_of_mm (init_clss (fst ?S))))"
    using not_bounded_nat_exists_larger[OF unbounded_f_g] by blast
  text \<open>The following does not hold anymore with the non-strict version of
    cardinality in the definition.\<close>
  { fix i
    assume "no_step cdcl\<^sub>W_stgy (fst (g i))"
    with g[of i]
    have False
      proof (induction rule: cdcl\<^sub>W_restart_with_restart.induct)
        case (restart_step T S n) note H = this(1) and c = this(2) and n_s = this(4)
        obtain S' where "cdcl\<^sub>W_stgy S S'"
          using H c by (metis gr_implies_not0 relpowp_E2)
        then show False using n_s by auto
      next
        case (restart_full S T)
        then show False unfolding full1_def by (auto dest: tranclpD)
      qed
    } note H = this
  obtain m T where
    m: "m = card (set_mset (learned_clss T)) - card (set_mset (learned_clss (fst (g k))))" and
    "m > f (snd (g k))" and
    "restart T (fst (g (k+1)))" and
    cdcl\<^sub>W_stgy: "(cdcl\<^sub>W_stgy ^^ m) (fst (g k)) T"
    using g[of k] H[of "Suc k"] by (force simp: cdcl\<^sub>W_restart_with_restart.simps full1_def)
  have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (fst (g k)) T"
    using cdcl\<^sub>W_stgy relpowp_imp_rtranclp by metis
  then have "cdcl\<^sub>W_all_struct_inv T"
    using inv[of k]  rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart by blast
  moreover have "card (set_mset (learned_clss T)) - card (set_mset (learned_clss (fst (g k))))
      > card (simple_clss (atms_of_mm (init_clss (fst ?S))))"
      unfolding m[symmetric] using \<open>m > f (snd (g k))\<close> f_g_k by linarith
    then have "card (set_mset (learned_clss T))
      > card (simple_clss (atms_of_mm (init_clss (fst ?S))))"
      by linarith
  moreover
    have "init_clss (fst (g k)) = init_clss T"
      using \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (fst (g k)) T\<close> rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart rtranclp_cdcl\<^sub>W_restart_init_clss
      inv unfolding cdcl\<^sub>W_all_struct_inv_def
      by blast
    then have "init_clss (fst ?S) = init_clss T"
      using init_g[of k] by auto
  ultimately show False
    using cdcl\<^sub>W_all_struct_inv_learned_clss_bound
    by (simp add: \<open>finite (atms_of_mm (init_clss (fst (g 0))))\<close> simple_clss_finite
      card_mono leD)
qed

lemma cdcl\<^sub>W_restart_with_restart_distinct_mset_clauses:
  assumes invR: "cdcl\<^sub>W_all_struct_inv (fst R)" and
  st: "cdcl\<^sub>W_restart_with_restart R S" and
  dist: "distinct_mset (clauses (fst R))" and
  R: \<open>no_smaller_propa (fst R)\<close>
  shows "distinct_mset (clauses (fst S))"
  using assms(2,1,3,4)
proof (induction)
  case (restart_full S T)
  then show ?case using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[of S T] unfolding full1_def
    by (auto dest: tranclp_into_rtranclp)
next
  case (restart_step T S n U)
  then have "distinct_mset (clauses T)" using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[of S T]
    unfolding full1_def by (auto dest: relpowp_imp_rtranclp)
  then show ?case using \<open>restart T U\<close> unfolding clauses_def
    by (metis distinct_mset_union fstI restartE subset_mset.le_iff_add union_assoc)
qed
end

locale luby_sequence =
  fixes ur :: nat (*unit run*)
  assumes "ur > 0"
begin

lemma exists_luby_decomp:
  fixes i ::nat
  shows "\<exists>k::nat. (2 ^ (k - 1) \<le> i \<and> i < 2 ^ k - 1) \<or> i = 2 ^ k - 1"
proof (induction i)
  case 0
  then show ?case
    by (rule exI[of _ 0], simp)
next
  case (Suc n)
  then obtain k where "2 ^ (k - 1) \<le> n \<and> n < 2 ^ k - 1 \<or> n = 2 ^ k - 1"
    by blast
  then consider
      (st_interv) "2 ^ (k - 1) \<le> n" and "n \<le> 2 ^ k - 2"
    | (end_interv) "2 ^ (k - 1) \<le> n" and "n = 2 ^ k - 2"
    | (pow2) "n = 2 ^ k - 1"
    by linarith
  then show ?case
    proof cases
      case st_interv
      then show ?thesis apply - apply (rule exI[of _ k])
        by (metis (no_types, lifting) One_nat_def Suc_diff_Suc Suc_lessI
          \<open>2 ^ (k - 1) \<le> n \<and> n < 2 ^ k - 1 \<or> n = 2 ^ k - 1\<close> diff_self_eq_0
          dual_order.trans le_SucI le_imp_less_Suc numeral_2_eq_2 one_le_numeral
          one_le_power zero_less_numeral zero_less_power)
    next
      case end_interv
      then show ?thesis apply - apply (rule exI[of _ k]) by auto
    next
      case pow2
      then show ?thesis apply - apply (rule exI[of _ "k+1"]) by auto
    qed
qed

text \<open>Luby sequences are defined by:
   \<^item> @{term "(2::nat)^(k::nat)- 1"}, if @{term "i = 2^k - 1"}
   \<^item> @{term "luby_sequence_core (i - (2::nat)^(k - 1) + 1)"}, if @{term "2^(k - 1) \<le> i"} and
   @{term "i \<le> 2^k - 1"}

Then the sequence is then scaled by a constant unit run (called @{term ur} here), strictly positive.
\<close>
function luby_sequence_core :: "nat \<Rightarrow> nat" where
"luby_sequence_core i =
  (if \<exists>k. i = 2^k - 1
  then 2^((SOME k. i = 2^k - 1) - 1)
  else luby_sequence_core (i - 2^((SOME k. 2^(k-1)\<le> i \<and> i < 2^k - 1) - 1) + 1))"
by auto
termination
proof (relation "less_than", goal_cases)
  case 1
  then show ?case by auto
next
  case (2 i)
  let ?k = "SOME k. 2 ^ (k - 1) \<le> i \<and> i < 2 ^ k - 1"
  have "2 ^ (?k - 1) \<le> i \<and> i < 2 ^ ?k - 1"
    apply (rule someI_ex)
    using "2" exists_luby_decomp by blast
  then show ?case
    (* sledgehammer *)
    proof -
      have "\<forall>n na. \<not> (1::nat) \<le> n \<or> 1 \<le> n ^ na"
        by (meson one_le_power)
      then have f1: "(1::nat) \<le> 2 ^ (?k - 1)"
        using one_le_numeral by blast
      have f2: "i - 2 ^ (?k - 1) + 2 ^ (?k - 1) = i"
        using \<open>2 ^ (?k - 1) \<le> i \<and> i < 2 ^ ?k - 1\<close> le_add_diff_inverse2 by blast
      have f3: "2 ^ ?k - 1 \<noteq> Suc 0"
        using f1 \<open>2 ^ (?k - 1) \<le> i \<and> i < 2 ^ ?k - 1\<close> by linarith
      have "2 ^ ?k - (1::nat) \<noteq> 0"
        using \<open>2 ^ (?k - 1) \<le> i \<and> i < 2 ^ ?k - 1\<close> gr_implies_not0 by blast
      then have f4: "2 ^ ?k \<noteq> (1::nat)"
        by linarith
      have f5: "\<forall>n na. if na = 0 then (n::nat) ^ na = 1 else n ^ na = n * n ^ (na - 1)"
        by (simp add: power_eq_if)
      then have "?k \<noteq> 0"
        using f4 by meson
      then have "2 ^ (?k - 1) \<noteq> Suc 0"
        using f5 f3 by presburger
      then have "Suc 0 < 2 ^ (?k - 1)"
        using f1 by linarith
      then show ?thesis
        using f2 less_than_iff by presburger
    qed
qed

function natlog2 :: "nat \<Rightarrow> nat" where
"natlog2 n = (if n = 0 then 0 else 1 + natlog2 (n div 2))"
  using not0_implies_Suc by auto
termination by (relation "measure (\<lambda>n. n)") auto

declare natlog2.simps[simp del]

declare luby_sequence_core.simps[simp del]

lemma two_pover_n_eq_two_power_n'_eq:
  assumes H: "(2::nat) ^ (k::nat) - 1 = 2 ^ k' - 1"
  shows "k' = k"
proof -
  have "(2::nat) ^ (k::nat) = 2 ^ k'"
    using H by (metis One_nat_def Suc_pred zero_less_numeral zero_less_power)
  then show ?thesis by simp
qed

lemma luby_sequence_core_two_power_minus_one:
  "luby_sequence_core (2^k - 1) = 2^(k-1)" (is "?L = ?K")
proof -
  have decomp: "\<exists>ka. 2 ^ k - 1 = 2 ^ ka - 1"
    by auto
  have "?L = 2^((SOME k'. (2::nat)^k - 1 = 2^k' - 1) - 1)"
    apply (subst luby_sequence_core.simps, subst decomp)
    by simp
  moreover have "(SOME k'. (2::nat)^k - 1 = 2^k' - 1) = k"
    apply (rule some_equality)
      apply simp
      using two_pover_n_eq_two_power_n'_eq by blast
  ultimately show ?thesis by presburger
qed

lemma different_luby_decomposition_false:
  assumes
    H: "2 ^ (k - Suc 0) \<le> i" and
    k': "i < 2 ^ k' - Suc 0" and
    k_k': "k > k'"
  shows "False"
proof -
  have "2 ^ k' - Suc 0 < 2 ^ (k - Suc 0)"
    using k_k' less_eq_Suc_le by auto
  then show ?thesis
    using H k' by linarith
qed

lemma luby_sequence_core_not_two_power_minus_one:
  assumes
    k_i: "2 ^ (k - 1) \<le> i" and
    i_k: "i < 2^ k - 1"
  shows "luby_sequence_core i = luby_sequence_core (i - 2 ^ (k - 1) + 1)"
proof -
  have H: "\<not> (\<exists>ka. i = 2 ^ ka - 1)"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain k'::nat where k': "i = 2 ^ k' - 1" by blast
      have "(2::nat) ^ k' - 1 < 2 ^ k - 1"
        using i_k unfolding k' .
      then have "(2::nat) ^ k' < 2 ^ k"
        by linarith
      then have "k' < k"
        by simp
      have "2 ^ (k - 1) \<le> 2 ^ k' - (1::nat)"
        using k_i unfolding k' .
      then have "(2::nat) ^ (k-1) < 2 ^ k'"
        by (metis Suc_diff_1 not_le not_less_eq zero_less_numeral zero_less_power)
      then have "k-1 < k'"
        by simp

      show False using \<open>k' < k\<close> \<open>k-1 < k'\<close> by linarith
    qed
  have "\<And>k k'. 2 ^ (k - Suc 0) \<le> i \<Longrightarrow> i < 2 ^ k - Suc 0 \<Longrightarrow> 2 ^ (k' - Suc 0) \<le> i \<Longrightarrow>
    i < 2 ^ k' - Suc 0 \<Longrightarrow> k = k'"
    by (meson different_luby_decomposition_false linorder_neqE_nat)
  then have k: "(SOME k. 2 ^ (k - Suc 0) \<le> i \<and> i < 2 ^ k - Suc 0) = k"
    using k_i i_k by auto
  show ?thesis
    apply (subst luby_sequence_core.simps[of i], subst H)
    by (simp add: k)
qed

lemma unbounded_luby_sequence_core: "unbounded luby_sequence_core"
  unfolding bounded_def
proof
  assume "\<exists>b. \<forall>n. luby_sequence_core n \<le> b"
  then obtain b where b: "\<And>n. luby_sequence_core n \<le> b"
    by metis
  have "luby_sequence_core (2^(b+1) - 1) = 2^b"
    using luby_sequence_core_two_power_minus_one[of "b+1"] by simp
  moreover have "(2::nat)^b > b"
    by (induction b) auto
  ultimately show False using b[of "2^(b+1) - 1"] by linarith
qed

abbreviation luby_sequence :: "nat \<Rightarrow> nat" where
"luby_sequence n \<equiv>  ur * luby_sequence_core n"

lemma bounded_luby_sequence: "unbounded luby_sequence"
  using bounded_const_product[of ur] luby_sequence_axioms
  luby_sequence_def unbounded_luby_sequence_core by blast

lemma luby_sequence_core_0: "luby_sequence_core 0 = 1"
proof -
  have 0: "(0::nat) = 2^0-1"
    by auto
  show ?thesis
    by (subst 0, subst luby_sequence_core_two_power_minus_one) simp
qed

lemma "luby_sequence_core n \<ge> 1"
proof (induction n rule: nat_less_induct_case)
  case 0
  then show ?case by (simp add: luby_sequence_core_0)
next
  case (Suc n) note IH = this

  consider
      (interv) k where "2 ^ (k - 1) \<le> Suc n" and "Suc n < 2 ^ k - 1"
    | (pow2)  k where "Suc n = 2 ^ k - Suc 0"
    using exists_luby_decomp[of "Suc n"] by auto

  then show ?case
     proof cases
       case pow2
       show ?thesis
         using luby_sequence_core_two_power_minus_one pow2 by auto
     next
       case interv
       have n: "Suc n - 2 ^ (k - 1) + 1 < Suc n"
         by (metis Suc_1 Suc_eq_plus1 add.commute add_diff_cancel_left' add_less_mono1 gr0I
           interv(1) interv(2) le_add_diff_inverse2 less_Suc_eq not_le power_0 power_one_right
           power_strict_increasing_iff)
       show ?thesis
         apply (subst luby_sequence_core_not_two_power_minus_one[OF interv])
         using IH n by auto
     qed
qed
end

locale luby_sequence_restart =
  luby_sequence ur +
  conflict_driven_clause_learning\<^sub>W
    \<comment> \<open>functions for the state: \<close>
    state_eq state
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>get state:\<close>
    init_state
  for
    ur :: nat and
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'b" and
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    hd_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lit" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and

    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st"
begin

sublocale cdcl\<^sub>W_restart_restart where
  f = luby_sequence
  apply unfold_locales
  using bounded_luby_sequence by blast

end
end
