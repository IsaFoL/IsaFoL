(*  Title:       Family_Extensions
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2019
*)

theory Redundancy_Criterion_Family_Extensions
  imports Dynamic_Completeness_Lifting

begin

locale consequence_relation_family =
  fixes
    Bot :: "'f set" and
    Q :: "'q set" and
    entails_q :: "'q \<Rightarrow> ('f set \<Rightarrow> 'f set \<Rightarrow> bool)"
  assumes
    Q_not_empty: "Q \<noteq> {}" and
    Bot_not_empty: "Bot \<noteq> {}" and
    q_cons_rel: "q \<in> Q \<Longrightarrow> consequence_relation Bot (entails_q q)"
begin

definition entails_Q :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>Q" 50) where
  "(N1 \<Turnstile>Q N2) = (\<forall>q \<in> Q. entails_q q N1 N2)"

paragraph \<open>Lemma 19 from the technical report\<close>
lemma cons_rel_family_is_cons_rel: "consequence_relation Bot entails_Q"
  unfolding consequence_relation_def
proof (intro conjI)
  show \<open>Bot \<noteq> {}\<close> using Bot_not_empty .
next
  show "\<forall>B N. B \<in> Bot \<longrightarrow> {B} \<Turnstile>Q N"
    unfolding entails_Q_def by (metis consequence_relation_def q_cons_rel)
next
  show "\<forall>N2 N1. N2 \<subseteq> N1 \<longrightarrow> N1 \<Turnstile>Q N2"
    unfolding entails_Q_def by (metis consequence_relation_def q_cons_rel)
next
  show "\<forall>N2 N1. (\<forall>C\<in>N2. N1 \<Turnstile>Q {C}) \<longrightarrow> N1 \<Turnstile>Q N2"
    unfolding entails_Q_def by (metis consequence_relation_def q_cons_rel)
next
  show "\<forall>N1 N2 N3. N1 \<Turnstile>Q N2 \<longrightarrow> N2 \<Turnstile>Q N3 \<longrightarrow> N1 \<Turnstile>Q N3"
    unfolding entails_Q_def by (metis consequence_relation_def q_cons_rel)
qed

end

locale calculus_with_red_crit_family = inference_system Inf + consequence_relation_family Bot Q entails_q
  for
    Bot :: "'f set" and
    Inf :: \<open>'f inference set\<close> and
    Q :: "'q set" and
    entails_q :: "'q \<Rightarrow> ('f set \<Rightarrow> 'f set \<Rightarrow> bool)"
  + fixes
    Red_Inf_q :: "'q \<Rightarrow> ('f set \<Rightarrow> 'f inference set)" and
    Red_F_q :: "'q \<Rightarrow> ('f set \<Rightarrow> 'f set)"
  assumes
    all_red_crit: "q \<in> Q \<Longrightarrow> calculus_with_red_crit Bot Inf (entails_q q) (Red_Inf_q q) (Red_F_q q)"
begin

definition Red_Inf_Q :: "'f set \<Rightarrow> 'f inference set" where
  "Red_Inf_Q N = \<Inter> {X N |X. X \<in> (Red_Inf_q ` Q)}"

definition Red_F_Q :: "'f set \<Rightarrow> 'f set" where
  "Red_F_Q N = \<Inter> {X N |X. X \<in> (Red_F_q ` Q)}"

paragraph \<open>Lemma 20 from the technical report\<close>
lemma inter_red_crit: "calculus_with_red_crit Bot Inf entails_Q Red_Inf_Q Red_F_Q"
  unfolding calculus_with_red_crit_def calculus_with_red_crit_axioms_def
proof (intro conjI)
  show "consequence_relation Bot entails_Q"
    using cons_rel_family_is_cons_rel .
next
  show "\<forall>N. Red_Inf_Q N \<subseteq> Inf"
    unfolding Red_Inf_Q_def
  proof
    fix N
    show "\<Inter> {X N |X. X \<in> Red_Inf_q ` Q} \<subseteq> Inf"
    proof (intro Inter_subset)
      fix Red_Infs
      assume one_red_inf: "Red_Infs \<in> {X N |X. X \<in> Red_Inf_q ` Q}"
      show "Red_Infs \<subseteq> Inf" using one_red_inf
      proof
        assume "\<exists>Red_Inf_qi. Red_Infs = Red_Inf_qi N \<and> Red_Inf_qi \<in> Red_Inf_q ` Q"
        then obtain Red_Inf_qi where
          red_infs_def: "Red_Infs = Red_Inf_qi N" and red_inf_qi_in: "Red_Inf_qi \<in> Red_Inf_q ` Q"
          by blast
        obtain qi where red_inf_qi_def: "Red_Inf_qi = Red_Inf_q qi" and qi_in: "qi \<in> Q"
          using red_inf_qi_in by blast
        show "Red_Infs \<subseteq> Inf"
          using all_red_crit[OF qi_in] calculus_with_red_crit.Red_Inf_to_Inf red_inf_qi_def
          red_infs_def by blast
      qed
    next
      show "{X N |X. X \<in> Red_Inf_q ` Q} \<noteq> {}" using Q_not_empty by blast
    qed
  qed
next
  show "\<forall>B N. B \<in> Bot \<longrightarrow> N \<Turnstile>Q {B} \<longrightarrow> N - Red_F_Q N \<Turnstile>Q {B}"
  proof (intro allI impI)
    fix B N
    assume
      B_in: "B \<in> Bot" and
      N_unsat: "N \<Turnstile>Q {B}"
    show "N - Red_F_Q N \<Turnstile>Q {B}" unfolding entails_Q_def Red_F_Q_def 
    proof
      fix qi
      assume qi_in: "qi \<in> Q"
      define entails_qi (infix "\<Turnstile>qi" 50) where "entails_qi = entails_q qi"
      have cons_rel_qi: "consequence_relation Bot entails_qi"
        unfolding entails_qi_def using all_red_crit[OF qi_in] calculus_with_red_crit.axioms(1) by blast
      define Red_F_qi where "Red_F_qi = Red_F_q qi"
      have red_qi_in_Q: "Red_F_Q N \<subseteq> Red_F_qi N"
        unfolding Red_F_Q_def Red_F_qi_def using image_iff qi_in by blast
      then have "N - (Red_F_qi N) \<subseteq> N - (Red_F_Q N)" by blast
      then have entails_1: "(N - Red_F_Q N) \<Turnstile>qi (N - Red_F_qi N)"
        using all_red_crit[OF qi_in]
        unfolding calculus_with_red_crit_def consequence_relation_def entails_qi_def by metis
      have N_unsat_qi: "N \<Turnstile>qi {B}" using qi_in N_unsat unfolding entails_qi_def entails_Q_def by simp
      then have N_unsat_qi: "(N - Red_F_qi N) \<Turnstile>qi {B}"
        using all_red_crit[OF qi_in] Red_F_qi_def calculus_with_red_crit.Red_F_Bot[OF _ B_in] entails_qi_def
        by fastforce
      show "(N - \<Inter> {X N |X. X \<in> Red_F_q ` Q}) \<Turnstile>qi {B}"
        using consequence_relation.entails_trans[OF cons_rel_qi entails_1 N_unsat_qi]
        unfolding Red_F_Q_def .
    qed
  qed
next
  show "\<forall>N1 N2. N1 \<subseteq> N2 \<longrightarrow> Red_F_Q N1 \<subseteq> Red_F_Q N2"
  proof (intro allI impI)
    fix N1 :: "'f set"
    and N2 :: "'f set"
    assume
      N1_in_N2: "N1 \<subseteq> N2"
    show "Red_F_Q N1 \<subseteq> Red_F_Q N2"
    proof
      fix x
      assume x_in: "x \<in> Red_F_Q N1"
      then have "\<forall>qi \<in> Q. x \<in> Red_F_q qi N1" unfolding Red_F_Q_def by blast
      then have "\<forall>qi \<in> Q. x \<in> Red_F_q qi N2"
        using N1_in_N2 all_red_crit calculus_with_red_crit.axioms(2) calculus_with_red_crit.Red_F_of_subset by blast
      then show "x \<in> Red_F_Q N2" unfolding Red_F_Q_def by blast
    qed
  qed
next
  show "\<forall>N1 N2. N1 \<subseteq> N2 \<longrightarrow> Red_Inf_Q N1 \<subseteq> Red_Inf_Q N2"
  proof (intro allI impI)
    fix N1 :: "'f set"
    and N2 :: "'f set"
    assume
      N1_in_N2: "N1 \<subseteq> N2"
    show "Red_Inf_Q N1 \<subseteq> Red_Inf_Q N2"
    proof
      fix x
      assume x_in: "x \<in> Red_Inf_Q N1"
      then have "\<forall>qi \<in> Q. x \<in> Red_Inf_q qi N1" unfolding Red_Inf_Q_def by blast
      then have "\<forall>qi \<in> Q. x \<in> Red_Inf_q qi N2"
        using N1_in_N2 all_red_crit calculus_with_red_crit.axioms(2) calculus_with_red_crit.Red_Inf_of_subset by blast
      then show "x \<in> Red_Inf_Q N2" unfolding Red_Inf_Q_def by blast
    qed
  qed
next
  show "\<forall>N2 N1. N2 \<subseteq> Red_F_Q N1 \<longrightarrow> Red_F_Q N1 \<subseteq> Red_F_Q (N1 - N2)"
  proof (intro allI impI)
    fix N2 N1
    assume N2_in_Red_N1: "N2 \<subseteq> Red_F_Q N1"
    show "Red_F_Q N1 \<subseteq> Red_F_Q (N1 - N2)"
    proof
      fix x
      assume x_in: "x \<in> Red_F_Q N1"
      then have "\<forall>qi \<in> Q. x \<in> Red_F_q qi N1" unfolding Red_F_Q_def by blast
      moreover have "\<forall>qi \<in> Q. N2 \<subseteq> Red_F_q qi N1" using N2_in_Red_N1 unfolding Red_F_Q_def by blast
      ultimately have "\<forall>qi \<in> Q. x \<in> Red_F_q qi (N1 - N2)"
        using all_red_crit calculus_with_red_crit.axioms(2) calculus_with_red_crit.Red_F_of_Red_F_subset by blast
      then show "x \<in> Red_F_Q (N1 - N2)" unfolding Red_F_Q_def by blast
    qed
  qed
next
  show "\<forall>N2 N1. N2 \<subseteq> Red_F_Q N1 \<longrightarrow> Red_Inf_Q N1 \<subseteq> Red_Inf_Q (N1 - N2)"
  proof (intro allI impI)
    fix N2 N1
    assume N2_in_Red_N1: "N2 \<subseteq> Red_F_Q N1"
    show "Red_Inf_Q N1 \<subseteq> Red_Inf_Q (N1 - N2)"
    proof
      fix x
      assume x_in: "x \<in> Red_Inf_Q N1"
      then have "\<forall>qi \<in> Q. x \<in> Red_Inf_q qi N1" unfolding Red_Inf_Q_def by blast
      moreover have "\<forall>qi \<in> Q. N2 \<subseteq> Red_F_q qi N1" using N2_in_Red_N1 unfolding Red_F_Q_def by blast
      ultimately have "\<forall>qi \<in> Q. x \<in> Red_Inf_q qi (N1 - N2)"
        using all_red_crit calculus_with_red_crit.axioms(2) calculus_with_red_crit.Red_Inf_of_Red_F_subset by blast
      then show "x \<in> Red_Inf_Q (N1 - N2)" unfolding Red_Inf_Q_def by blast
    qed
  qed
next
  show "\<forall>\<iota> N. \<iota> \<in> Inf \<longrightarrow> concl_of \<iota> \<in> N \<longrightarrow> \<iota> \<in> Red_Inf_Q N"
  proof (intro allI impI)
    fix \<iota> N
    assume
      i_in: "\<iota> \<in> Inf" and
      concl_in: "concl_of \<iota> \<in> N"
    then have "\<forall>qi \<in> Q. \<iota> \<in> Red_Inf_q qi N"
      using all_red_crit calculus_with_red_crit.axioms(2) calculus_with_red_crit.Red_Inf_of_Inf_to_N by blast
    then show "\<iota> \<in> Red_Inf_Q N" unfolding Red_Inf_Q_def by blast
  qed
qed

sublocale inter_red_crit_calculus: calculus_with_red_crit
  where Bot=Bot
  and Inf=Inf
  and entails=entails_Q
  and Red_Inf=Red_Inf_Q
  and Red_F=Red_F_Q
  using inter_red_crit .

paragraph \<open>Lemma 21 from the technical report\<close>
lemma "calculus_with_red_crit.saturated Inf Red_Inf_Q N \<longleftrightarrow>
  (\<forall>qi \<in> Q. calculus_with_red_crit.saturated Inf (Red_Inf_q qi) N)" for N
proof
  fix N
  assume inter_sat: "calculus_with_red_crit.saturated Inf Red_Inf_Q N"
  show "\<forall>qi \<in> Q. calculus_with_red_crit.saturated Inf (Red_Inf_q qi) N"
  proof
    fix qi
    assume qi_in: "qi \<in> Q"
    interpret one: calculus_with_red_crit Bot Inf "entails_q qi" "Red_Inf_q qi" "Red_F_q qi"
      by (rule all_red_crit[OF qi_in])
    show "one.saturated N"
      using qi_in inter_sat unfolding one.saturated_def inter_red_crit_calculus.saturated_def Red_Inf_Q_def 
      by blast
  qed
next
  fix N
  assume all_sat: "\<forall>qi \<in> Q. calculus_with_red_crit.saturated Inf (Red_Inf_q qi) N"
  show "inter_red_crit_calculus.saturated N" unfolding inter_red_crit_calculus.saturated_def Red_Inf_Q_def 
  proof
    fix x
    assume x_in: "x \<in> Inf_from N"
    have "\<forall>Red_Inf_qi \<in> Red_Inf_q ` Q. x \<in> Red_Inf_qi N" 
    proof
      fix Red_Inf_qi
      assume red_inf_in: "Red_Inf_qi \<in> Red_Inf_q ` Q"
      then obtain qi where red_inf_qi_def: "Red_Inf_qi = Red_Inf_q qi" and qi_in: "qi \<in> Q" by blast
      interpret one: calculus_with_red_crit Bot Inf "entails_q qi" "Red_Inf_q qi" "Red_F_q qi"
        by (rule all_red_crit[OF qi_in])
      have "one.saturated N" using all_sat qi_in red_inf_qi_def by blast
      then show "x \<in> Red_Inf_qi N" unfolding one.saturated_def using x_in red_inf_qi_def by blast
    qed
    then show "x \<in> \<Inter> {X N |X. X \<in> Red_Inf_q ` Q}" by blast
  qed
qed

paragraph \<open>Lemma 22 from the technical report\<close>
lemma
  "\<forall>N. (calculus_with_red_crit.saturated Inf Red_Inf_Q N \<and> (\<forall>B \<in> Bot. B \<notin> N)) \<longrightarrow>  (\<exists>B \<in> Bot. \<exists>qi \<in> Q. \<not> entails_q qi N {B})
    \<Longrightarrow> static_refutational_complete_calculus Bot Inf entails_Q Red_Inf_Q Red_F_Q"
proof (rule ccontr)
  assume
    N_saturated: "\<forall>N. (calculus_with_red_crit.saturated Inf Red_Inf_Q N \<and> (\<forall>B \<in> Bot. B \<notin> N)) \<longrightarrow>  (\<exists>B \<in> Bot. \<exists>qi \<in> Q. \<not> entails_q qi N {B})" and
    no_stat_ref_comp: "\<not> static_refutational_complete_calculus Bot Inf (\<Turnstile>Q) Red_Inf_Q Red_F_Q"
  obtain N1 B1 where B1_in: "B1 \<in> Bot" and N1_saturated: "calculus_with_red_crit.saturated Inf Red_Inf_Q N1" and
    N1_unsat: "N1 \<Turnstile>Q {B1}" and no_B_in_N1: "\<forall>B \<in> Bot. B \<notin> N1"
    using no_stat_ref_comp by (metis inter_red_crit static_refutational_complete_calculus.intro
      static_refutational_complete_calculus_axioms.intro)
  obtain B2 qi where no_qi:"\<not> entails_q qi N1 {B2}" and qi_in: "qi \<in> Q" using N_saturated N1_saturated no_B_in_N1 by blast
  have "N1 \<Turnstile>Q {B2}" using N1_unsat B1_in cons_rel_family_is_cons_rel unfolding consequence_relation_def by metis
  then have "entails_q qi N1 {B2}" unfolding entails_Q_def using qi_in by blast
  then show "False" using no_qi by simp
qed

end

subsection \<open>Intersection of Liftings\<close>

locale lifting_equivalence_with_red_crit_family = Non_ground: inference_system Inf_F
  + Ground_family: calculus_with_red_crit_family Bot_G Inf_G Q entails_q Red_Inf_q Red_F_q
  for
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    Inf_G :: \<open>'g inference set\<close> and
    Q :: "'q set" and
    entails_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g set \<Rightarrow> bool)" and
    Red_Inf_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g inference set)" and
    Red_F_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g set)"
  + fixes
    Bot_F :: "'f set" and
    \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set" and
    \<G>_Inf_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set" and
    Prec_F_g :: "'g \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool"
  assumes
    Q_not_empty: "Q \<noteq> {}" and
    standard_lifting_family: "q \<in> Q \<Longrightarrow> lifting_with_wf_ordering_family Bot_F Inf_F Bot_G (entails_q q) Inf_G (Red_Inf_q q) (Red_F_q q) (\<G>_F_q q) (\<G>_Inf_q q) Prec_F_g" 
begin

definition \<G>_set_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'g set" where
  "\<G>_set_q q N \<equiv> UNION N (\<G>_F_q q)"

definition Red_Inf_\<G>_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f inference set" where
  "Red_Inf_\<G>_q q N = {\<iota> \<in> Inf_F. \<G>_Inf_q q \<iota> \<subseteq> Red_Inf_q q (\<G>_set_q q N)}"

definition Red_Inf_\<G>_Q :: "'f set \<Rightarrow> 'f inference set" where
  "Red_Inf_\<G>_Q N = \<Inter> {X N |X. X \<in> (Red_Inf_\<G>_q ` Q)}"


definition Red_F_\<G>_empty_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_empty_q q N = {C. \<forall>D \<in> \<G>_F_q q C. D \<in> Red_F_q q (\<G>_set_q q N) \<or> (\<exists>E \<in> N. Empty_Order E C \<and> D \<in> \<G>_F_q q E)}"

definition Red_F_\<G>_empty :: "'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_empty N = \<Inter> {X N |X. X \<in> (Red_F_\<G>_empty_q ` Q)}"

definition Red_F_\<G>_q_g :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_q_g q N = {C. \<forall>D \<in> \<G>_F_q q C. D \<in> Red_F_q q (\<G>_set_q q N) \<or> (\<exists>E \<in> N. Prec_F_g D E C \<and> D \<in> \<G>_F_q q E)}"

definition Red_F_\<G>_g :: "'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_g N = \<Inter> {X N |X. X \<in> (Red_F_\<G>_q_g ` Q)}"

definition entails_\<G>_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> bool" where
  "entails_\<G>_q q N1 N2 \<equiv> entails_q q (\<G>_set_q q N1) (\<G>_set_q q N2)"

definition entails_\<G>_Q :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" where
  "entails_\<G>_Q N1 N2 \<equiv> \<forall>q\<in>Q. entails_\<G>_q q N1 N2"

lemma red_crit_lifting_family:
  "q \<in> Q \<Longrightarrow> calculus_with_red_crit Bot_F Inf_F (entails_\<G>_q q) (Red_Inf_\<G>_q q) (Red_F_\<G>_q_g q)"
proof -
  fix q
  assume q_in: "q \<in> Q"
  interpret wf_lift:
    lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q q" Inf_G "Red_Inf_q q" "Red_F_q q" "\<G>_F_q q" "\<G>_Inf_q q" Prec_F_g
    using standard_lifting_family[OF q_in] .
  have "entails_\<G>_q q = wf_lift.entails_\<G>"
    unfolding entails_\<G>_q_def wf_lift.entails_\<G>_def \<G>_set_q_def by blast
  moreover have "Red_Inf_\<G>_q q = wf_lift.Red_Inf_\<G>"
    unfolding Red_Inf_\<G>_q_def \<G>_set_q_def wf_lift.Red_Inf_\<G>_def by blast
  moreover have "Red_F_\<G>_q_g q = wf_lift.Red_F_\<G>"
    unfolding Red_F_\<G>_q_g_def \<G>_set_q_def wf_lift.Red_F_\<G>_def by blast
  ultimately show "calculus_with_red_crit Bot_F Inf_F (entails_\<G>_q q) (Red_Inf_\<G>_q q) (Red_F_\<G>_q_g q)"
    using wf_lift.lifted_calculus_with_red_crit.calculus_with_red_crit_axioms by simp
qed


lemma red_crit_lifting_family_empty_ord:
  "q \<in> Q \<Longrightarrow> calculus_with_red_crit Bot_F Inf_F (entails_\<G>_q q) (Red_Inf_\<G>_q q) (Red_F_\<G>_empty_q q)"
proof -
  fix q
  assume q_in: "q \<in> Q"
  interpret wf_lift:
    lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q q" Inf_G "Red_Inf_q q" "Red_F_q q" "\<G>_F_q q" "\<G>_Inf_q q" Prec_F_g
    using standard_lifting_family[OF q_in] .
  have "entails_\<G>_q q = wf_lift.entails_\<G>"
    unfolding entails_\<G>_q_def wf_lift.entails_\<G>_def \<G>_set_q_def by blast
  moreover have "Red_Inf_\<G>_q q = wf_lift.Red_Inf_\<G>"
    unfolding Red_Inf_\<G>_q_def \<G>_set_q_def wf_lift.Red_Inf_\<G>_def by blast
  moreover have "Red_F_\<G>_empty_q q = wf_lift.empty_order_lifting.Red_F_\<G>"
    unfolding Red_F_\<G>_empty_q_def \<G>_set_q_def wf_lift.empty_order_lifting.Red_F_\<G>_def by blast
  ultimately show "calculus_with_red_crit Bot_F Inf_F (entails_\<G>_q q) (Red_Inf_\<G>_q q) (Red_F_\<G>_empty_q q)"
    using wf_lift.empty_order_lifting.lifted_calculus_with_red_crit.calculus_with_red_crit_axioms
    by simp
qed

lemma cons_rel_fam_Q_lem: \<open>consequence_relation_family Bot_F Q entails_\<G>_q\<close>
proof
  show \<open>Q \<noteq> {}\<close> by (rule Q_not_empty)
next
  show "Bot_F \<noteq> {}"
    using standard_lifting_family Q_not_empty
    by (meson ex_in_conv lifting_with_wf_ordering_family.axioms(1) standard_lifting.Bot_F_not_empty)
next
  fix qi
  assume "qi \<in> Q"
  show "Bot_F \<noteq> {}"
    using standard_lifting_family Q_not_empty
    by (meson ex_in_conv lifting_with_wf_ordering_family.axioms(1) standard_lifting.Bot_F_not_empty)
next
  fix qi B N1
  assume
    qi_in: "qi \<in> Q" and
    B_in: "B \<in> Bot_F"
  interpret lift: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q qi" Inf_G "Red_Inf_q qi" "Red_F_q qi" "\<G>_F_q qi" "\<G>_Inf_q qi" Prec_F_g
    by (rule standard_lifting_family[OF qi_in])
  have "(entails_\<G>_q qi) = lift.entails_\<G>"
    unfolding entails_\<G>_q_def lift.entails_\<G>_def \<G>_set_q_def by simp
  then show "entails_\<G>_q qi {B} N1"
    using B_in lift.lifted_consequence_relation.bot_implies_all by auto
next
  fix qi and N2 N1::"'f set"
  assume
    qi_in: "qi \<in> Q" and
    N_incl: "N2 \<subseteq> N1"
  interpret lift: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q qi" Inf_G "Red_Inf_q qi" "Red_F_q qi" "\<G>_F_q qi" "\<G>_Inf_q qi" Prec_F_g
    by (rule standard_lifting_family[OF qi_in])
  have "(entails_\<G>_q qi) = lift.entails_\<G>"
    unfolding entails_\<G>_q_def lift.entails_\<G>_def \<G>_set_q_def by simp
  then show "entails_\<G>_q qi N1 N2"
    using N_incl by (simp add: lift.lifted_consequence_relation.subset_entailed)
next
  fix qi N1 N2
  assume
    qi_in: "qi \<in> Q" and
    all_C: "\<forall>C\<in> N2. entails_\<G>_q qi N1 {C}"
  interpret lift: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q qi" Inf_G "Red_Inf_q qi" "Red_F_q qi" "\<G>_F_q qi" "\<G>_Inf_q qi" Prec_F_g
    by (rule standard_lifting_family[OF qi_in])
  have "(entails_\<G>_q qi) = lift.entails_\<G>"
    unfolding entails_\<G>_q_def lift.entails_\<G>_def \<G>_set_q_def by simp
  then show "entails_\<G>_q qi N1 N2"
    using all_C lift.lifted_consequence_relation.all_formulas_entailed by presburger
next
  fix qi N1 N2 N3
  assume
    qi_in: "qi \<in> Q" and
    entails12: "entails_\<G>_q qi N1 N2" and
    entails23: "entails_\<G>_q qi N2 N3"
  interpret lift: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q qi" Inf_G "Red_Inf_q qi" "Red_F_q qi" "\<G>_F_q qi" "\<G>_Inf_q qi" Prec_F_g
    by (rule standard_lifting_family[OF qi_in])
  have "(entails_\<G>_q qi) = lift.entails_\<G>"
    unfolding entails_\<G>_q_def lift.entails_\<G>_def \<G>_set_q_def by simp
  then show "entails_\<G>_q qi N1 N3"
    using entails12 entails23 lift.lifted_consequence_relation.entails_trans by presburger
qed

interpretation cons_rel_Q: consequence_relation Bot_F entails_\<G>_Q
proof -
  interpret cons_rel_fam: consequence_relation_family Bot_F Q entails_\<G>_q
    by (rule cons_rel_fam_Q_lem)
  have "consequence_relation_family.entails_Q Q entails_\<G>_q = entails_\<G>_Q"
    unfolding entails_\<G>_Q_def cons_rel_fam.entails_Q_def by (simp add: entails_\<G>_q_def)
  then show "consequence_relation Bot_F entails_\<G>_Q"
    using consequence_relation_family.cons_rel_family_is_cons_rel[OF cons_rel_fam_Q_lem] by simp
qed

sublocale lifted_calc_w_red_crit_family:
  calculus_with_red_crit_family Bot_F Inf_F Q entails_\<G>_q Red_Inf_\<G>_q Red_F_\<G>_q_g
  using cons_rel_fam_Q_lem red_crit_lifting_family
  by (simp add: calculus_with_red_crit_family.intro calculus_with_red_crit_family_axioms_def)

lemma "calculus_with_red_crit Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_g"
proof -
  have "lifted_calc_w_red_crit_family.entails_Q = entails_\<G>_Q"
    unfolding entails_\<G>_Q_def lifted_calc_w_red_crit_family.entails_Q_def by simp
  moreover have "lifted_calc_w_red_crit_family.Red_Inf_Q = Red_Inf_\<G>_Q"
    unfolding Red_Inf_\<G>_Q_def lifted_calc_w_red_crit_family.Red_Inf_Q_def by simp 
  moreover have "lifted_calc_w_red_crit_family.Red_F_Q = Red_F_\<G>_g"
    unfolding Red_F_\<G>_g_def lifted_calc_w_red_crit_family.Red_F_Q_def by simp
  ultimately show "calculus_with_red_crit Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_g"
  using lifted_calc_w_red_crit_family.inter_red_crit by simp
qed

sublocale empty_ord_lifted_calc_w_red_crit_family:
  calculus_with_red_crit_family Bot_F Inf_F Q entails_\<G>_q Red_Inf_\<G>_q Red_F_\<G>_empty_q
  using cons_rel_fam_Q_lem red_crit_lifting_family_empty_ord
  by (simp add: calculus_with_red_crit_family.intro calculus_with_red_crit_family_axioms_def)

find_theorems name: lifted_calc_w_red_crit_family name: empty

lemma "calculus_with_red_crit Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_empty"
proof -
  have "lifted_calc_w_red_crit_family.entails_Q = entails_\<G>_Q"
    unfolding entails_\<G>_Q_def lifted_calc_w_red_crit_family.entails_Q_def by simp
  moreover have "empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q = Red_Inf_\<G>_Q"
    unfolding Red_Inf_\<G>_Q_def lifted_calc_w_red_crit_family.Red_Inf_Q_def by simp 
  moreover have "empty_ord_lifted_calc_w_red_crit_family.Red_F_Q = Red_F_\<G>_empty"
    unfolding Red_F_\<G>_empty_def empty_ord_lifted_calc_w_red_crit_family.Red_F_Q_def by simp
  ultimately show "calculus_with_red_crit Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_empty"
  using empty_ord_lifted_calc_w_red_crit_family.inter_red_crit by simp
qed

end

end