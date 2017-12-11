(*  Title:       A Fair Ordered Resolution Prover for First-Order Clauses with Weights
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>A Fair Ordered Resolution Prover for First-Order Clauses with Weights\<close>

text \<open>
TODO. Formalizes footnote.
\<close>

theory Weighted_FO_Ordered_Resolution_Prover
  imports FO_Ordered_Resolution_Prover
begin

type_synonym 'a wclause = "'a clause \<times> nat"
type_synonym 'a wstate = "'a wclause multiset \<times> 'a wclause multiset \<times> 'a wclause multiset \<times> nat"

fun state_of_wstate :: "'a wstate \<Rightarrow> 'a state" where
  "state_of_wstate (N, P, Q, n) =
   (set_mset (image_mset fst N), set_mset (image_mset fst P), set_mset (image_mset fst Q))"

locale weighted_FO_resolution_prover =
  FO_resolution_prover S subst_atm id_subst comp_subst renamings_apart atm_of_atms mgu less_atm
  for
    S :: "('a :: wellorder) clause \<Rightarrow> 'a clause" and
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a clause list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes
    weight :: "'a clause \<times> nat \<Rightarrow> nat"
  assumes
    weight_mono: "m < n \<Longrightarrow> weight (C, m) < weight (C, n)"
begin

(* FIXME: don't use \<circ> in abbreviations -- fragile w.r.t. simplifier when applied *)
abbreviation clss_of_wstate :: "'a wstate \<Rightarrow> 'a clause set" where
  "clss_of_wstate \<equiv> clss_of_state \<circ> state_of_wstate"

abbreviation N_of_wstate :: "'a wstate \<Rightarrow> 'a clause set" where
  "N_of_wstate \<equiv> N_of_state \<circ> state_of_wstate"

abbreviation P_of_wstate :: "'a wstate \<Rightarrow> 'a clause set" where
  "P_of_wstate \<equiv> P_of_state \<circ> state_of_wstate"

abbreviation Q_of_wstate :: "'a wstate \<Rightarrow> 'a clause set" where
  "Q_of_wstate \<equiv> Q_of_state \<circ> state_of_wstate"

abbreviation grounding_of_wstate :: "'a wstate \<Rightarrow> 'a clause set" where
  "grounding_of_wstate St \<equiv> grounding_of_state (state_of_wstate St)"

abbreviation Liminf_wstate :: "'a wstate llist \<Rightarrow> 'a state" where
  "Liminf_wstate Sts \<equiv> Liminf_state (lmap state_of_wstate Sts)"

lemma generation_le_weight: "n \<le> weight (C, n)"
  by (induct n, simp, metis weight_mono[of k "Suc k" for k] Suc_le_eq le_less le_trans)

inductive weighted_RP :: "'a wstate \<Rightarrow> 'a wstate \<Rightarrow> bool" (infix "\<leadsto>\<^sub>w" 50) where
  tautology_deletion: "Neg A \<in># C \<Longrightarrow> Pos A \<in># C \<Longrightarrow> (N + {#(C, i)#}, P, Q, n) \<leadsto>\<^sub>w (N, P, Q, n)"
| forward_subsumption: "D \<in># image_mset fst (P + Q) \<Longrightarrow> subsumes D C \<Longrightarrow>
    (N + {#(C, i)#}, P, Q, n) \<leadsto>\<^sub>w (N, P, Q, n)"
| backward_subsumption_P: "D \<in># image_mset fst N \<Longrightarrow> C \<in># image_mset fst P \<Longrightarrow>
    strictly_subsumes D C \<Longrightarrow> (N, P, Q, n) \<leadsto>\<^sub>w (N, {#(E, k) \<in># P. E \<noteq> C#}, Q, n)"
| backward_subsumption_Q: "D \<in># image_mset fst N \<Longrightarrow> strictly_subsumes D C \<Longrightarrow>
    (N, P, Q + {#(C, i)#}, n) \<leadsto>\<^sub>w (N, P, Q, n)"
| forward_reduction: "D + {#L'#} \<in># image_mset fst (P + Q) \<Longrightarrow> - L = L' \<cdot>l \<sigma> \<Longrightarrow> D \<cdot> \<sigma> \<subseteq># C \<Longrightarrow>
    (N + {#(C + {#L#}, i)#}, P, Q, n) \<leadsto>\<^sub>w (N + {#(C, i)#}, P, Q, n)"
| backward_reduction_P: "D + {#L'#} \<in># image_mset fst N \<Longrightarrow> - L = L' \<cdot>l \<sigma> \<Longrightarrow> D \<cdot> \<sigma> \<subseteq># C \<Longrightarrow>
    (\<forall>j. (C + {#L#}, j) \<in># P \<longrightarrow> j \<le> i) \<Longrightarrow>
    (N, P + {#(C + {#L#}, i)#}, Q, n) \<leadsto>\<^sub>w (N, P + {#(C, i)#}, Q, n)"
| backward_reduction_Q: "D + {#L'#} \<in># image_mset fst N \<Longrightarrow> - L = L' \<cdot>l \<sigma> \<Longrightarrow> D \<cdot> \<sigma> \<subseteq># C \<Longrightarrow>
    (N, P, Q + {#(C + {#L#}, i)#}, n) \<leadsto>\<^sub>w (N, P + {#(C, i)#}, Q, n)"
| clause_processing: "(N + {#(C, i)#}, P, Q, n) \<leadsto>\<^sub>w (N, P + {#(C, i)#}, Q, n)"
| inference_computation: "(\<forall>(D, j) \<in># P. weight (C, i) \<le> weight (D, j)) \<Longrightarrow>
    N = mset_set ((\<lambda>D. (D, n)) ` concls_of
      (inference_system.inferences_between (ord_FO_\<Gamma> S) (set_mset (image_mset fst Q)) C)) \<Longrightarrow>
    ({#}, P + {#(C, i)#}, Q, n) \<leadsto>\<^sub>w (N, {#(D, j) \<in># P. D \<noteq> C#}, Q + {#(C, i)#}, Suc n)"

lemma weighted_RP_imp_RP: "St \<leadsto>\<^sub>w St' \<Longrightarrow> state_of_wstate St \<leadsto> state_of_wstate St'"
proof (induction rule: weighted_RP.induct)
  case (backward_subsumption_P D N C P Q n)
  show ?case
    by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>", OF _ _
          RP.backward_subsumption_P[of D "fst ` set_mset N" C "fst ` set_mset P - {C}"
            "fst ` set_mset Q"]])
      (use backward_subsumption_P in auto)
next
  case (inference_computation P C i N n Q)
  show ?case
     by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>", OF _ _
           RP.inference_computation[of "fst ` set_mset N" "fst ` set_mset Q" C
             "fst ` set_mset P - {C}"]],
         use inference_computation(2) finite_ord_FO_resolution_inferences_between
           in \<open>auto simp: comp_def image_comp inference_system.inferences_between_def\<close>)
qed (use RP.intros in simp_all)

(* FIXME: turn into "if and only iff" *)
lemma final_weighted_RP: "\<not> ({#}, {#}, Q, n) \<leadsto>\<^sub>w St"
  by (auto elim: weighted_RP.cases)

context
  fixes
    Sts :: "'a wstate llist"
  assumes
    full_deriv: "full_chain (op \<leadsto>\<^sub>w) Sts" and
    finite_Sts0: "finite (clss_of_wstate (lhd Sts))" and
    empty_P0: "P_of_wstate (lhd Sts) = {}" and
    empty_Q0: "Q_of_wstate (lhd Sts) = {}"
begin

lemmas deriv = full_chain_imp_chain[OF full_deriv]
lemmas lhd_lmap_Sts = llist.map_sel(1)[OF chain_not_lnull[OF deriv]]

lemma deriv_RP: "chain (op \<leadsto>) (lmap state_of_wstate Sts)"
  using deriv weighted_RP_imp_RP by (metis chain_lmap)

lemma finite_Sts0_RP: "finite (clss_of_state (lhd (lmap state_of_wstate Sts)))"
  using finite_Sts0 chain_length_pos[OF deriv] by auto

lemma empty_P0_RP: "P_of_state (lhd (lmap state_of_wstate Sts)) = {}"
  using empty_P0 chain_length_pos[OF deriv] by auto

lemma empty_Q0_RP: "Q_of_state (lhd (lmap state_of_wstate Sts)) = {}"
  using empty_Q0 chain_length_pos[OF deriv] by auto

lemmas Sts_thms = deriv_RP finite_Sts0_RP empty_P0_RP empty_Q0_RP

lemma weighted_RP_model:
  assumes step: "St \<leadsto>\<^sub>w St'"
  shows "I \<Turnstile>s grounding_of_wstate St' \<longleftrightarrow> I \<Turnstile>s grounding_of_wstate St"
  using RP_model[OF Sts_thms weighted_RP_imp_RP[OF step]] by (simp only: comp_def)

abbreviation S_gQ :: "'a clause \<Rightarrow> 'a clause" where
  "S_gQ \<equiv> S_Q (lmap state_of_wstate Sts)"

interpretation sq: selection S_gQ
  unfolding S_Q_def[OF Sts_thms] using S_M_selects_subseteq S_M_selects_neg_lits selection_axioms
  by unfold_locales blast

interpretation gd: ground_resolution_with_selection S_gQ
  by unfold_locales

interpretation src: standard_redundancy_criterion_reductive gd.ord_\<Gamma>
  by unfold_locales

interpretation src: standard_redundancy_criterion_counterex_reducing gd.ord_\<Gamma>
  "ground_resolution_with_selection.INTERP S_gQ"
  by unfold_locales

lemmas ord_\<Gamma>_saturated_upto_def = src.saturated_upto_def
lemmas ord_\<Gamma>_saturated_upto_complete = src.saturated_upto_complete
lemmas ord_\<Gamma>_contradiction_Rf = src.contradiction_Rf

lemma weighted_RP_sound:
  assumes "{#} \<in> clss_of_state (Liminf_wstate Sts)"
  shows "\<not> satisfiable (grounding_of_wstate (lhd Sts))"
  by (rule RP_sound[OF Sts_thms assms, unfolded lhd_lmap_Sts])

find_theorems \<infinity> llength
find_theorems lfinite llength
find_theorems chain lfinite

lemma llength_infinite_if_Ns_non_empty: (* This is only true for full derivations. *)
  assumes "\<forall>i<llength Sts. N_of_state (state_of_wstate (lnth Sts i)) \<noteq> {}"
  shows "llength Sts = \<infinity>"
  using assms deriv
  oops

abbreviation RP_measure :: "nat \<Rightarrow> 'a wstate \<Rightarrow> _" where
  "RP_measure max_gen \<equiv> (\<lambda>(N, P, Q, n). (image_mset (\<lambda>(_, i). max_gen - i) (N + P), 
                                          sum_mset (image_mset (\<lambda>(C, i). Suc (size C)) (N + P + Q)),
                                          size N))"

abbreviation RP_measure2 :: "nat \<Rightarrow> 'a wstate \<Rightarrow> _" where
  "RP_measure2 max_gen \<equiv> (\<lambda>(N, P, Q, n). (image_mset (\<lambda>(C, i). (max_gen - i, size C)) (N + P), 
                                          size N))"

abbreviation RP_relation where
  "RP_relation \<equiv> mult natLess <*lex*> natLess <*lex*> natLess"

abbreviation RP_relation2 where
  "RP_relation2 \<equiv> mult (natLess <*lex*> natLess) <*lex*> natLess"

term "((RP_measure max_gen St),(RP_measure max_gen St2)) \<in> RP_relation"
term "((RP_measure2 max_gen St),(RP_measure2 max_gen St)) \<in> RP_relation2"

(* FIXME: Move this. *)
fun wN_of_wstate :: "'a wstate \<Rightarrow> 'a wclause multiset" where
  "wN_of_wstate (N, P, Q, n) = N"

fun wP_of_wstate :: "'a wstate \<Rightarrow> 'a wclause multiset" where
  "wP_of_wstate (N, P, Q, n) = P"

fun wQ_of_wstate :: "'a wstate \<Rightarrow> 'a wclause multiset" where
  "wQ_of_wstate (N, P, Q, n) = Q"

fun n_of_wstate :: "'a wstate \<Rightarrow> nat" where
  "n_of_wstate (N, P, Q, n) = n"

lemma of_wstate_split[simp]: "(wN_of_wstate St, wP_of_wstate St, wQ_of_wstate St, n_of_wstate St) = St"
  by (cases St) auto

find_consts "_ wstate \<Rightarrow> nat"

term "fst (a,b)"

lemma wf_natLess: "wf natLess"
  unfolding natLess_def using wf_less by auto

lemma wf_RP_relation: "wf RP_relation"
  using wf_natLess wf_mult by auto

lemma 
  assumes "St \<leadsto>\<^sub>w St'"
  assumes "(C,i) \<in># wP_of_wstate St"
  shows "(RP_measure (weight (C,i) + 1) St', RP_measure (weight (C,i) + 1) St) \<in> RP_relation"
  using assms proof (induction rule: weighted_RP.induct)
  case (tautology_deletion A C' N i' P Q n)
  have "(fst (RP_measure (weight (C, i) + 1) (N, P, Q, n)), fst (RP_measure (weight (C, i) + 1) (N + {#(C', i')#}, P, Q, n))) \<in> mult natLess"
    by (rule subset_implies_mult) auto
  then show ?case
    unfolding lex_prod_def by auto
next
  case (forward_subsumption D P Q C' N i' n)
  have "(fst (RP_measure (weight (C, i) + 1) (N, P, Q, n)), fst (RP_measure (weight (C, i) + 1) (N + {#(C', i')#}, P, Q, n))) \<in> mult natLess"
    by (rule subset_implies_mult) auto
  then show ?case
    unfolding lex_prod_def by auto
next
  case (backward_subsumption_P D N C' P Q n)
  then show ?case sorry
next
  case (backward_subsumption_Q D N C' P Q i' n)
  have "(fst (RP_measure (weight (C, i) + 1) (N, P, Q, n))) = fst (RP_measure (weight (C, i) + 1) (N, P, Q  + {#(C', i')#}, n))"
    by auto
  moreover have "(fst (snd (RP_measure (weight (C, i) + 1) (N, P, Q, n))), fst (snd (RP_measure (weight (C, i) + 1) (N + {#(C', i')#}, P, Q, n)))) \<in> natLess"
    by (simp add: natLess_def)
  ultimately show ?case
    unfolding lex_prod_def by force
next
  case (forward_reduction D L' P Q L \<sigma> C' N i' n)
  have "(fst (RP_measure (weight (C, i) + 1) (N + {#(C', i')#}, P, Q, n))) = fst (RP_measure (weight (C, i) + 1) (N + {#(C' + {#L#}, i')#}, P, Q, n))"
    by auto
  moreover have "(fst (snd (RP_measure (weight (C, i) + 1) (N + {#(C', i')#}, P, Q, n))), fst (snd (RP_measure (weight (C, i) + 1) (N + {#(C' + {#L#}, i')#}, P, Q, n)))) \<in> natLess"
     by (simp add: natLess_def)
  ultimately show ?case
    unfolding lex_prod_def by force
next
  case (backward_reduction_P D L' N L \<sigma> C' P i' Q n)
  have "(fst (RP_measure (weight (C, i) + 1) (N, P + {#(C', i')#}, Q, n))) = fst (RP_measure (weight (C, i) + 1) (N, P + {#(C' + {#L#}, i')#}, Q, n))"
    by auto
  moreover have "(fst (snd (RP_measure (weight (C, i) + 1) (N, P + {#(C', i')#}, Q, n))), fst (snd (RP_measure (weight (C, i) + 1) (N, P  + {#(C' + {#L#}, i')#}, Q, n)))) \<in> natLess"
     by (simp add: natLess_def)
  ultimately show ?case
    unfolding lex_prod_def by force
next
  case (backward_reduction_Q D L' N L \<sigma> C' P Q i' n)
  have "(fst (RP_measure (weight (C, i) + 1) (N, P + {#(C', i')#}, Q , n))) = fst (RP_measure (weight (C, i) + 1) (N, P, Q  + {#(C' + {#L#}, i')#}, n))"
    sorry (* Problem is... here the measure actually grows *)
  moreover have "(fst (snd (RP_measure (weight (C, i) + 1) (N, P + {#(C', i')#}, Q, n))), fst (snd (RP_measure (weight (C, i) + 1) (N, P  + {#(C' + {#L#}, i')#}, Q, n)))) \<in> natLess"
     by (simp add: natLess_def)
  ultimately show ?case
    unfolding lex_prod_def by force
next
  case (clause_processing N C i P Q n)
  then show ?case sorry
next
  case (inference_computation P C i N n Q)
  then show ?case sorry
qed


lemma stay_or_delete_completely':
  assumes "St \<leadsto>\<^sub>w St'" "(C,i) \<in># wP_of_wstate St"
  shows "(\<exists>j\<le>i.(C, j) \<in># wP_of_wstate St') \<or> (\<forall>j. (C, j) \<notin># wP_of_wstate St')"
using assms proof (induction rule: weighted_RP.induct)
  case (tautology_deletion A C N i P Q n)
  then show ?case 
    by auto
next
  case (forward_subsumption D P Q C N i' n)
  then show ?case 
    by auto
next
  case (backward_subsumption_P D N C P Q n)
  then show ?case 
    by auto
next
  case (backward_subsumption_Q D N C P Q i' n)
  then show ?case 
    by auto
next
  case (forward_reduction D L' P Q L \<sigma> C N i' n)
  then show ?case 
    by auto
next
  case (backward_reduction_P D L' N L \<sigma> C' P i' Q n)
  then show ?case 
  proof (cases "C = C' + {#L#}")
    case True
    note True_outer = this
    then show ?thesis
    proof (cases "count (image_mset fst P) C = 0")
      case True
      then have "C \<notin># image_mset fst P"
        using not_in_iff by metis
      then have "\<forall>j. (C, j) \<notin># P"
        sorry
      then have "\<forall>j. (C, j) \<notin># P + {#(C', i')#}"
        using True_outer by auto
      then have "\<forall>j. (C, j) \<notin># wP_of_wstate (N, P + {#(C', i')#}, Q, n)"
        by auto
      then show ?thesis 
        by auto
    next
      case False
      then have "C \<in># image_mset fst P"
        using not_in_iff by metis
      then obtain k where k_p: "(C, k) \<in># P + {#(C', i')#}"
        sorry
      then have k_i': "k \<le> i'"
        using backward_reduction_P unfolding True_outer by auto

      have "(C, i) \<in># P + {#(C' + {#L#}, i')#}"
        using backward_reduction_P True_outer by auto

      then have "\<exists>j\<le>i. (C, j) \<in># P + {#(C', i')#}"
        using k_p k_i' by auto 
         (* I remove the biggest, but know that there is one smaller *)
      then have "\<exists>j\<le>i. (C, j) \<in># wP_of_wstate (N, P + {#(C', i')#}, Q, n)"
        by auto
      then show ?thesis
        by auto
    qed
  next
    case False
    then have "(C, i) \<in># P"
      using backward_reduction_P by auto
    then show ?thesis
      by auto
  qed
next
  case (backward_reduction_Q D L' N L \<sigma> C P Q i n)
  then show ?case by auto
next
  case (clause_processing N C i P Q n)
  then show ?case by auto
next
  case (inference_computation P C i N n Q)
  then show ?case by auto
qed

(* FIXME: Come up with a better name. *)
lemma stay_or_delete_completely: (* This is only true for full derivations. *)
  assumes "enat (Suc k) < llength Sts"
  assumes a: "(C, i) \<in># wP_of_wstate (lnth Sts k)"
  shows "(\<exists>j\<le>i. (C, j) \<in># wP_of_wstate (lnth Sts (Suc k))) \<or> (\<forall>j. (C, j) \<notin># wP_of_wstate (lnth Sts (Suc k)))"
proof -
  from deriv have "lnth Sts k \<leadsto>\<^sub>w lnth Sts (Suc k)"
    using assms chain_lnth_rel by auto
  then show ?thesis
    using stay_or_delete_completely'[of "lnth Sts k" "lnth Sts (Suc k)" C i] a by blast
qed

(* FIXME: come up with better name *)
lemma persistent_wclause_if_persistent_clause:
  assumes llength_infty: "llength Sts = \<infinity>"
  assumes "C \<in> Liminf_llist (lmap P_of_state (lmap state_of_wstate Sts))"
  shows "\<exists>i. (C, i) \<in> Liminf_llist (lmap (set_mset \<circ> wP_of_wstate) Sts)"
proof -
  from assms obtain x where x_p:
    "enat x < llength Sts"
    "\<And>xa. x \<le> xa \<Longrightarrow> enat xa < llength Sts \<Longrightarrow> C \<in> P_of_state (state_of_wstate (lnth Sts xa))"
    unfolding Liminf_llist_def by auto
  have "\<exists>i. (C,i) \<in># wP_of_wstate (lnth Sts x)"
  proof -
    from x_p have "C \<in> P_of_state (state_of_wstate (lnth Sts x))"
      by auto
    then show ?thesis
      by (cases "(lnth Sts x)") auto
  qed
  then obtain i where i_p:
    "(C,i) \<in># wP_of_wstate (lnth Sts x)"
    by auto
  have "\<forall>xa. enat xa < llength (ldrop x Sts) \<longrightarrow> C \<in> P_of_state (state_of_wstate (lnth (ldrop x Sts) xa))"
  proof (rule, rule) (* FIXME: should this be a lemma? *)
    fix xa :: "nat"
    assume "enat xa < llength (ldrop (enat x) Sts)"
    then have llen: "enat x + enat xa < llength  Sts"
      using llength_infty by auto
    then have "enat (x + xa) < llength  Sts"
      by auto
    then have "C \<in> P_of_state (state_of_wstate (lnth Sts (xa + x)))"
      using x_p(2)[of "x + xa"] by (simp add: add.commute) 
    then show "C \<in> P_of_state (state_of_wstate (lnth (ldrop (enat x) Sts) xa))"
      using lnth_ldrop[of "enat x" xa Sts] using llen by auto
  qed

  thm stay_or_delete_completely
  have "\<exists>f. \<forall>i. f i \<in># wP_of_wstate ((lnth (ldrop x Sts) i)) \<and> fst (f i) \<ge> fst (f (Suc i)) \<and> fst (f i) = fst (f (Suc i))"
    sorry

  have Ci_stays: "(\<And>xa. enat xa < llength Sts \<Longrightarrow> (C, i) \<in># wP_of_wstate (lnth (ldrop x Sts) xa))"
  subgoal for xa
    proof (induction xa)
      case 0
      then show ?case 
        using i_p lnth_ldrop[of 0 x Sts] llength_infty by auto
    next
      case (Suc xa)
      then have "(C, i) \<in># wP_of_wstate (lnth (ldrop (enat x) Sts) xa)"
        by (simp add: llength_infty)
      then have "(C, i) \<in># wP_of_wstate (lnth Sts (x + xa))"
        by (simp add: add.commute llength_infty)
      moreover have "\<exists>j. (C,j) \<in># lnth (lmap wP_of_wstate Sts) (Suc (x + xa))"
      proof -
        from x_p(1) x_p(2) have "C \<in> P_of_state (state_of_wstate (lnth Sts (Suc (x + xa))))"
          using llength_infty by auto
        then have "\<exists>j. (C, j) \<in># wP_of_wstate (lnth Sts (Suc (x + xa)))"
          by (cases "(lnth Sts (Suc (x + xa)))") auto
        then show ?thesis
          by (simp add: llength_infty)
      qed
      ultimately have "(C, i) \<in># lnth (lmap wP_of_wstate Sts) (Suc (x + xa))"
        using stay_or_delete_completely llength_infty sorry (* FIXME: The whole proof needs a substantial change -- or maybe I can change the lemma! *)
      then show ?case
        by (simp add: add.commute llength_infty)
    qed
    done
  have "(\<And>xa. x \<le> xa \<Longrightarrow> enat xa < llength Sts \<Longrightarrow> (C, i) \<in># wP_of_wstate (lnth Sts xa))"
  proof -
    fix xa :: "nat"
    assume a:
      "x \<le> xa" 
      "enat xa < llength Sts"
    then have "enat (xa - x) < llength Sts"
      by (simp add: llength_infty)
    then have "(C, i) \<in># wP_of_wstate (lnth (ldrop x Sts) (xa - x))"
      using Ci_stays[of "xa - x"] by auto
    then show "(C, i) \<in># wP_of_wstate (lnth Sts xa)"
      using lnth_ldrop[of x "xa - x" Sts] a by auto
  qed
  then have "(C, i) \<in> Liminf_llist (lmap (set_mset \<circ> wP_of_wstate) Sts)"
    unfolding Liminf_llist_def using x_p by auto
  then show "\<exists>i. (C, i) \<in> Liminf_llist (lmap (set_mset \<circ> wP_of_wstate) Sts)"
    by auto
qed

lemma lfinite_not_LNil_nth_llast:
  assumes "lfinite Sts" "Sts \<noteq> LNil"
  shows "\<exists>i < llength Sts. lnth Sts i = llast Sts \<and> (\<forall>j < llength Sts. j \<le> i)"
using assms proof (induction rule: lfinite.induct)
  case lfinite_LNil
  then show ?case by auto
next
  case (lfinite_LConsI xs x)
  then show ?case
  proof (cases "xs = LNil")
    case True
    then have "lnth (LCons x xs) 0 = llast (LCons x xs)"
      using lfinite_LConsI by auto
    moreover 
    from True have "enat 0 < llength (LCons x xs)"
      using lfinite_LConsI enat_0 by auto 
    moreover
    from True have "\<forall>j<llength (LCons x xs). j \<le> enat 0"
      using lfinite_LConsI enat_0 by auto
    ultimately show ?thesis
      using lfinite_LConsI by auto
  next
    case False
    then obtain i where i_p: "enat i < llength xs \<and> lnth xs i = llast xs \<and> (\<forall>j<llength xs. j \<le> enat i)"
      using lfinite_LConsI by auto
    then have "enat (Suc i) < llength (LCons x xs)"
      by (simp add: Suc_ile_eq)
    moreover from i_p have "lnth (LCons x xs) (Suc i) = llast (LCons x xs)"
      by (metis gr_implies_not_zero llast_LCons llength_lnull lnth_Suc_LCons)
    moreover from i_p have "\<forall>j<llength (LCons x xs). j \<le> enat (Suc i)"
      by (metis antisym_conv2 eSuc_enat eSuc_ile_mono ileI1 iless_Suc_eq llength_LCons)
    ultimately show ?thesis
      by auto
  qed
qed  

lemma infinite_if_not_fair:
  assumes "\<not> fair_state_seq (lmap state_of_wstate Sts)"
  shows "\<not> lfinite Sts"
proof (rule ccontr)
  assume "\<not> \<not> lfinite Sts"
  then have "lfinite Sts"
    by auto
  then have no_inf_from_last: "\<forall>y. \<not> llast Sts \<leadsto>\<^sub>w y" 
    using full_chain_iff_chain[of "op \<leadsto>\<^sub>w" Sts] full_deriv by auto
  
  from assms obtain C where
    "C \<in> Liminf_llist (lmap N_of_state (lmap state_of_wstate Sts))
       \<union> Liminf_llist (lmap P_of_state (lmap state_of_wstate Sts))"
    unfolding fair_state_seq_def Liminf_state_def by auto
  then obtain i where i_p:
    "enat i < llength Sts"
    "\<And>j. i \<le> j \<Longrightarrow> enat j < llength Sts \<Longrightarrow> C \<in> N_of_state (state_of_wstate (lnth Sts j)) \<union> P_of_state (state_of_wstate (lnth Sts j))"
    unfolding Liminf_llist_def by auto
 
  have C_in_llast: "C \<in> N_of_state (state_of_wstate (llast Sts)) \<union> P_of_state (state_of_wstate (llast Sts))"
  proof -
    obtain l where l_p: "enat l < llength Sts \<and> lnth Sts l = llast Sts \<and> (\<forall>j<llength Sts. j \<le> enat l)"
      using \<open>lfinite Sts\<close> lfinite_not_LNil_nth_llast
      using i_p(1) by fastforce
    moreover
    then have "i \<le> l" 
      using i_p(1) by auto
    ultimately have
      "C \<in> N_of_state (state_of_wstate (lnth Sts l)) \<union> P_of_state (state_of_wstate (lnth Sts l))"
      using i_p(2)[of l] by auto
    then show "?thesis"
      using l_p by auto
  qed

  define N where "N = wN_of_wstate (llast Sts)"
  define P where "P = wP_of_wstate (llast Sts)"
  define Q where "Q = wQ_of_wstate (llast Sts)"
  define n where "n = n_of_wstate (llast Sts)"

  {
    assume "N_of_state (state_of_wstate (llast Sts)) \<noteq> {}"
    then obtain D j where "(D, j) \<in># N"
      unfolding N_def by (cases "llast Sts") auto
    then have "llast Sts \<leadsto>\<^sub>w (N - {#(D, j)#}, P + {#(D, j)#}, Q, n)"
      using weighted_RP.clause_processing[of "N - {#(D, j)#}" D j P Q n]
      unfolding N_def P_def Q_def n_def by auto
    then have "\<exists>St'. llast Sts \<leadsto>\<^sub>w St'"
      by auto
  }
  moreover
  {
    assume a: "N_of_state (state_of_wstate (llast Sts)) = {}"
    then have b: "N = {#}"
      unfolding N_def by (cases "llast Sts") auto
    from a have "C \<in> P_of_state (state_of_wstate (llast Sts))"
      using C_in_llast by auto
    then obtain D j where "(D, j) \<in># P"
      unfolding P_def by  (cases "llast Sts") auto
    then obtain D j where min: "(\<forall>(D', j') \<in># P - {#(D, j)#}. weight (D, j) \<le> weight (D', j'))"
      and Dj_in_p:"(D, j) \<in># P"
      sorry
    define N' where "N' = mset_set ((\<lambda>D'. (D', n)) ` concls_of (inference_system.inferences_between (ord_FO_\<Gamma> S) (set_mset (image_mset fst Q)) D))"
    have "llast Sts \<leadsto>\<^sub>w (N', {#(D', j') \<in># P - {# (D, j) #}. D' \<noteq> D#}, Q + {#(D,j)#}, Suc n)"
      using weighted_RP.inference_computation[of "P - {#(D, j)#}" D j N' n Q, OF min N'_def]
      using of_wstate_split[symmetric, of "llast Sts"]
      unfolding N_def[symmetric] P_def[symmetric]  Q_def[symmetric]  n_def[symmetric] 
      unfolding b
      using Dj_in_p by auto
    then have "\<exists>St'. llast Sts \<leadsto>\<^sub>w St'"
      by auto
  }
  ultimately have "\<exists>St'. llast Sts \<leadsto>\<^sub>w St'"
     by auto
   then show "False"
     using no_inf_from_last by metis
qed

theorem weighted_RP_fair: "fair_state_seq (lmap state_of_wstate Sts)"
proof (rule ccontr)
  assume asm: "\<not> fair_state_seq (lmap state_of_wstate Sts)"
  then have "\<not> lfinite Sts" using infinite_if_not_fair
    by auto
  then have inf: "llength Sts = \<infinity>"
    using llength_eq_infty_conv_lfinite by auto
  from asm obtain C where
    "C \<in> Liminf_llist (lmap N_of_state (lmap state_of_wstate Sts))
       \<union> Liminf_llist (lmap P_of_state (lmap state_of_wstate Sts))"
    unfolding fair_state_seq_def Liminf_state_def by auto
  then show False
  proof
    assume "C \<in> Liminf_llist (lmap N_of_state (lmap state_of_wstate Sts))"
    then obtain i where "(C, i) \<in> Liminf_llist (lmap (set_mset \<circ> wN_of_wstate) Sts)" 
      using persistent_wclause_if_persistent_clause[of C] inf sorry (* You need a persistent_wclause_if_persistent_clause for N *)
    then obtain k where k_p: "enat k < llength Sts"
      "\<And>j. k \<le> j \<Longrightarrow> enat j < llength Sts \<Longrightarrow> (C, i) \<in># wN_of_wstate (lnth Sts j)"
      unfolding Liminf_llist_def by auto
    from this(1) have "chain op \<leadsto>\<^sub>w (ldrop k Sts)"
      using deriv sorry
    moreover
    from k_p have "\<And>j. enat j < llength (ldrop k Sts) \<Longrightarrow> (C, i) \<in># wN_of_wstate (lnth (ldrop k Sts) j)"
      sorry
 (* 
    ultimately
    have neighbours in "map RP_measure (drop j)" are related by RP_relation  //by an appropriate lemma 
    then have FALSE since the relation is well founded. *)
    then show False
      sorry (* *)
  next
    assume asm: "C \<in> Liminf_llist (lmap P_of_state (lmap state_of_wstate Sts))"
    from asm obtain i where i_p:
      "enat i < llength Sts"
      "\<And>j. i \<le> j \<and> enat j < llength Sts \<Longrightarrow> C \<in> P_of_state (state_of_wstate (lnth Sts j))"
      unfolding Liminf_llist_def by auto
    then obtain i where "(C, i) \<in> Liminf_llist (lmap (set_mset \<circ> wP_of_wstate) Sts)"
      using persistent_wclause_if_persistent_clause[of C] using asm inf by auto
    then show False
      sorry
  qed
qed

corollary weighted_RP_saturated: "src.saturated_upto (Liminf_llist (lmap grounding_of_wstate Sts))"
  using RP_saturated_if_fair[OF Sts_thms weighted_RP_fair, unfolded llist.map_comp] by simp

corollary weighted_RP_complete:
  assumes "\<not> satisfiable (grounding_of_wstate (lhd Sts))"
  shows "{#} \<in> Q_of_state (Liminf_wstate Sts)"
  using assms RP_complete_if_fair[OF Sts_thms weighted_RP_fair, simplified lhd_lmap_Sts] by blast

end

end

(* FIXME: inherit "weighted_FO_resolution_prover" directly? *)
locale weighted_FO_resolution_prover_with_size_generation_factors =
  FO_resolution_prover S subst_atm id_subst comp_subst renamings_apart atm_of_atms mgu less_atm
  for
    S :: "('a :: wellorder) clause \<Rightarrow> 'a clause" and
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a literal multiset list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes
    size_atm :: "'a \<Rightarrow> nat" and
    size_factor :: nat and
    generation_factor :: nat
  assumes
    generation_factor_pos: "generation_factor > 0"
begin

fun weight :: "'a wclause \<Rightarrow> nat" where
  "weight (C, m) = size_factor * size_multiset (size_literal size_atm) C + generation_factor * m"

lemma weight_mono: "m < n \<Longrightarrow> weight (C, m) < weight (C, n)"
  using generation_factor_pos by simp

declare weight.simps [simp del]

sublocale wrp: weighted_FO_resolution_prover _ _ _ _ _ _ _ _ weight
  by unfold_locales (rule weight_mono)

notation wrp.weighted_RP (infix "\<leadsto>\<^sub>w" 50)

end

end
