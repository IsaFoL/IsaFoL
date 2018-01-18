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

definition weighted_RP_Non_Inference :: "'a wstate \<Rightarrow> 'a wstate \<Rightarrow> bool" (infix "\<leadsto>\<^sub>w\<^sub>n\<^sub>i" 50) where
  "St \<leadsto>\<^sub>w\<^sub>n\<^sub>i St' \<longleftrightarrow> St \<leadsto>\<^sub>w St' \<and> N_of_wstate St \<noteq> {}"

definition weighted_RP_Inference :: "'a wstate \<Rightarrow> 'a wstate \<Rightarrow> bool" (infix "\<leadsto>\<^sub>w\<^sub>i" 50) where
  "St \<leadsto>\<^sub>w\<^sub>i St' \<longleftrightarrow> St \<leadsto>\<^sub>w St' \<and> N_of_wstate St = {}"

lemma weighted_RP_iff_inference_or_non_inference: "St \<leadsto>\<^sub>w St' \<longleftrightarrow> St \<leadsto>\<^sub>w\<^sub>i St' \<or> St \<leadsto>\<^sub>w\<^sub>n\<^sub>i St'"
  unfolding weighted_RP_Non_Inference_def weighted_RP_Inference_def by auto

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

abbreviation RP_filtered_measure :: "('a wclause \<Rightarrow> bool) \<Rightarrow> 'a wstate \<Rightarrow> nat \<times> nat \<times> nat" where
  "RP_filtered_measure \<equiv> (\<lambda>p (N, P, Q, n). 
                              (sum_mset (image_mset (\<lambda>(C, i). Suc (size C)) {#Di \<in># N + P + Q. p Di#}), size {#Di \<in># N. p Di#}, size {#Di \<in># P. p Di#}))"

abbreviation RP_combined_measure_new :: "nat \<Rightarrow> 'a wstate \<Rightarrow> _" where
  "RP_combined_measure_new \<equiv> (\<lambda>w St. ((w + 1) - n_of_wstate St, RP_filtered_measure (\<lambda>(C, i). i \<le> w) St, RP_filtered_measure (\<lambda>Ci. True) St))"

abbreviation(input) RP_filtered_relation_new where
  "RP_filtered_relation_new \<equiv> natLess <*lex*> natLess <*lex*> natLess"

abbreviation(input) RP_combined_relation_new where
  "RP_combined_relation_new \<equiv> natLess <*lex*> RP_filtered_relation_new <*lex*> RP_filtered_relation_new"

term "(RP_combined_measure_new w St, RP_combined_measure_new w St2) \<in> RP_combined_relation_new"

(* FIXME: these should probably be avioded *)
abbreviation "(fst3 :: 'b * 'c * 'd \<Rightarrow> 'b) == fst"
abbreviation "(snd3 :: 'b * 'c * 'd \<Rightarrow> 'c) == \<lambda>x. fst (snd x)"
abbreviation "(trd3 :: 'b * 'c * 'd \<Rightarrow> 'd) == \<lambda>x. snd (snd x)"

lemma wf_natLess: "wf natLess"
  unfolding natLess_def using wf_less by auto

lemma wf_RP_filtered_relation: "wf RP_filtered_relation_new"
  using wf_natLess wf_mult by auto

lemma wf_RP_combined_relation_new: "wf RP_combined_relation_new"
  using wf_natLess wf_mult by auto

lemma weighted_RP_if_weighted_RP_Non_Inference: "St \<leadsto>\<^sub>w\<^sub>n\<^sub>i St' \<Longrightarrow> St \<leadsto>\<^sub>w St'"
  unfolding weighted_RP_Non_Inference_def by auto

lemma weighted_RP_if_weighted_RP_Inference: "St \<leadsto>\<^sub>w\<^sub>i St' \<Longrightarrow> St \<leadsto>\<^sub>w St'"
  unfolding weighted_RP_Inference_def by auto

lemma multiset_sum_of_Suc_f_monotone:
  assumes "N \<subset># M"
  shows "(\<Sum>x\<in>#N. Suc (f x)) < (\<Sum>x\<in>#M. Suc (f x))"
  using assms
proof (induction N arbitrary: M)
  case empty
  then obtain y where "y\<in>#M"
    by force
  then have "(\<Sum>x\<in>#M. 1) = (\<Sum>x\<in>#M - {# y #} + {# y #}. 1)"
    by auto
  also have "... = (\<Sum>x\<in>#M - {# y #}. 1) + (\<Sum>x\<in>#{# y #}. 1)"
    by (metis image_mset_union sum_mset.union)
  also have "... > (0 :: nat)"
    by auto
  finally have "0 < (\<Sum>x\<in>#M. Suc (f x))"
    using gr_zeroI by fastforce
  then show ?case 
    using empty by auto
next
  case (add x N)
  from this(2) have "(\<Sum>y\<in>#N. Suc (f y)) < (\<Sum>y\<in>#M - {#x#}. Suc (f y))"
    using add(1)[of "M - {#x#}"]
    by (simp add: insert_union_subset_iff)
  then show ?case
    by (smt Suc_le_eq add.prems add_Suc_right add_le_cancel_left insert_DiffM mset_subset_insertD sum_mset.insert)
qed

lemma multiset_sum_monotone_f':
  assumes "CC \<subset># DD"
  shows "(\<Sum>(C,i)\<in>#CC. Suc (f C)) < (\<Sum>(C,i)\<in>#DD. Suc (f C))"
  using multiset_sum_of_Suc_f_monotone[OF assms, of "f o fst"]
  by (metis (mono_tags, lifting) comp_apply image_mset_cong2 split_beta)

lemma filter_mset_strict_subset:
  assumes "x \<in># M"
  assumes "\<not>p x"
  shows "{#y \<in># M. p y#} \<subset># M"
proof -
  have subseteq: "{#E \<in># M. p E#} \<subseteq># M"
    by auto
  have "count {#E \<in># M. p E#} x = 0"
    using assms by auto
  moreover
  have "0 < count M x"
    using assms by auto
  ultimately have lt_count: "count {#y \<in># M. p y#} x < count M x"
    by auto
  then show ?thesis
    using subseteq by (metis less_not_refl2 subset_mset.le_neq_trans)  
qed

(* FIXME: rename *)
lemma weighted_RP_Non_Inference_measure_decreasing:
  assumes "St \<leadsto>\<^sub>w\<^sub>n\<^sub>i St'"
  shows "((RP_filtered_measure (\<lambda>Ci. True)) St', (RP_filtered_measure (\<lambda>Ci. True)) St) \<in> RP_filtered_relation_new"
using weighted_RP_if_weighted_RP_Non_Inference[OF assms(1)] using assms proof (induction rule: weighted_RP.induct)
  case (tautology_deletion A C' N i' P Q n)
  then show ?case
    unfolding natLess_def by auto
next
  case (forward_subsumption D P Q C' N i' n)
  then show ?case
    unfolding natLess_def by auto
next
  case (backward_subsumption_P D N C' P Q n)
  then obtain i' where  "(C',i') \<in># P"
    by auto
  then have "{#(E, k) \<in># P. E \<noteq> C'#} \<subset># P"
    using filter_mset_strict_subset[of "(C', i')" P "\<lambda>X. \<not>fst X =  C'"]
    by (metis (mono_tags, lifting) filter_mset_cong fst_conv prod.case_eq_if)
  then have "(\<Sum>(C, i)\<in>#{#(E, k) \<in># P. E \<noteq> C'#}. Suc (size C)) < (\<Sum>(C, i)\<in>#P. Suc (size C))"
    using multiset_sum_monotone_f'[of "{#(E, k) \<in># P. E \<noteq> C'#}" P size] by metis
  then have "fst ((RP_filtered_measure (\<lambda>Ci. True)) (N, {#(E, k) \<in># P. E \<noteq> C'#}, Q, n)) < fst ((RP_filtered_measure (\<lambda>Ci. True)) (N, P, Q, n))"
    by simp
  then show ?case
    unfolding natLess_def by auto
next
  case (backward_subsumption_Q D N C' P Q i' n)
  then show ?case
    unfolding natLess_def by auto
next
  case (forward_reduction D L' P Q L \<sigma> C' N i n)
  then show ?case
    unfolding natLess_def by auto
next
  case (backward_reduction_P D L' N L \<sigma> C' P i Q n)
  then show ?case
    unfolding natLess_def by auto
next
  case (backward_reduction_Q D L' N L \<sigma> C' P Q i n)
  then show ?case
    unfolding natLess_def by auto
next
  case (clause_processing N C' i P Q n)
  then show ?case
    unfolding natLess_def by auto
next
  case (inference_computation P C' i N n Q)
  then show ?case
    unfolding weighted_RP_Non_Inference_def by auto
qed

(* FIXME: move to an appropriate library. *)
lemma filter_mset_empty_if_finite_and_filter_set_empty:
  assumes 
    "{x \<in> X. P x} = {}" and
    "finite X"
  shows "{#x \<in># mset_set X. P x#} = {#}"
proof -
  have empty_empty: "\<And>Y. set_mset Y = {} \<Longrightarrow> Y = {#}"
    by auto
  from assms have "set_mset {#x \<in># mset_set X. P x#} = {}"
    by auto
  then show ?thesis
    by (rule empty_empty)
qed

lemma weighted_RP_Inference_has_measure2:
  assumes "St \<leadsto>\<^sub>w St'"
  assumes "(C, i) \<in># wP_of_wstate St"
  shows "(RP_combined_measure_new (weight (C, i)) St', RP_combined_measure_new (weight (C, i)) St) \<in> RP_combined_relation_new"
using assms proof (induction rule: weighted_RP.induct)
  case (tautology_deletion A C' N i' P Q n)
  then show ?case 
    unfolding natLess_def by auto
next
  case (forward_subsumption D P Q C' N i' n)
  then show ?case 
    unfolding natLess_def by auto
next
  case (backward_subsumption_P D N C' P Q n)
  define St where "St = (N, P, Q, n)"
  define P' where "P' = {#(E, k) \<in># P. E \<noteq> C'#}"
  define St' where "St' = (N, P', Q, n)"
  from backward_subsumption_P obtain i' where  "(C',i') \<in># P"
    by auto
  then have P'_sub_P: "P' \<subset># P"
    unfolding P'_def
    using filter_mset_strict_subset[of "(C', i')" P "\<lambda>X. \<not>fst X =  C'"]
    by (metis (mono_tags, lifting) filter_mset_cong fst_conv prod.case_eq_if)
  have P'_subeq_P_filter: "{#(Ca, ia) \<in># P'. ia \<le> weight (C, i)#} \<subseteq># {#(Ca, ia) \<in># P. ia \<le> weight (C, i)#}"
    apply (rule multiset_filter_mono) using P'_sub_P by auto
  
  (* First component *)
  have "fst3 (RP_combined_measure_new (weight (C, i)) St') \<le> fst3 (RP_combined_measure_new (weight (C, i)) St)" 
    unfolding St'_def St_def by auto
  moreover
  (* Second component *)
  from P'_subeq_P_filter have "(\<Sum>x\<in>#{#(Ca, ia) \<in># P'. ia \<le> weight (C, i)#}. case x of (C, i) \<Rightarrow> Suc (size C))
    \<le> (\<Sum>x\<in>#{#(Ca, ia) \<in># P. ia \<le> weight (C, i)#}. case x of (C, i) \<Rightarrow> Suc (size C))"
    by (rule sum_image_mset_mono)
  then have "fst3 (snd3 (RP_combined_measure_new (weight (C, i)) St')) \<le> fst3 (snd3 (RP_combined_measure_new (weight (C, i)) St))" 
    unfolding St'_def St_def by auto
  moreover
  have "snd3 (snd3 (RP_combined_measure_new (weight (C, i)) St')) \<le> snd3 (snd3 (RP_combined_measure_new (weight (C, i)) St))" 
    unfolding St'_def St_def by auto
  moreover
  from P'_subeq_P_filter have "size {#(Ca, ia) \<in># P'. ia \<le> weight (C, i)#} \<le> size {#(Ca, ia) \<in># P. ia \<le> weight (C, i)#}"
    by (simp add: size_mset_mono)
  then have "trd3 (snd3 (RP_combined_measure_new (weight (C, i)) St')) \<le> trd3 (snd3 (RP_combined_measure_new (weight (C, i)) St))" 
    unfolding St'_def St_def unfolding fst_def snd_def by auto
  (* Third component *)
  moreover
  from P'_sub_P have "(\<Sum>(C, i)\<in>#P'. Suc (size C)) < (\<Sum>(C, i)\<in>#P. Suc (size C))"
    using multiset_sum_monotone_f'[of "{#(E, k) \<in># P. E \<noteq> C'#}" P size]
    unfolding P'_def by metis
  then have "fst3 (trd3 (RP_combined_measure_new (weight (C, i)) St')) < fst3 (trd3 (RP_combined_measure_new (weight (C, i)) St))" 
    unfolding P'_def St'_def St_def by auto 
  ultimately show ?case
    unfolding natLess_def P'_def St'_def St_def by auto
next
  case (backward_subsumption_Q D N C' P Q i' n)
  then show ?case 
    unfolding natLess_def by auto
next
  case (forward_reduction D L' P Q L \<sigma> C' N i' n)
  then show ?case 
    unfolding natLess_def by auto
next
  case (backward_reduction_P D L' N L \<sigma> C' P i' Q n)
  then show ?case 
    unfolding natLess_def by auto
next
  case (backward_reduction_Q D L' N L \<sigma> C' P Q i' n)
  then show ?case 
    unfolding natLess_def by auto
next
  case (clause_processing N C' i' P Q n)
  then show ?case 
    unfolding natLess_def by auto
next
  case (inference_computation P C' i' N n Q)
  then show ?case 
  proof (cases "n \<le> weight (C, i)")
    case True
    then have "(weight (C, i) + 1) - n > (weight (C, i) + 1) - (Suc n)"
      by auto
    then show ?thesis 
      unfolding natLess_def by auto
  next
    case False
    define St :: "'a wstate" where "St = ({#}, P + {#(C', i')#}, Q, n)"
    define St' :: "'a wstate" where "St' =  (N, {#(D, j) \<in># P. D \<noteq> C'#}, Q + {#(C', i')#}, Suc n)"
    define concls where "concls = ((\<lambda>D. (D, n)) ` concls_of (inference_system.inferences_between (ord_FO_\<Gamma> S) (fst ` set_mset Q) C'))"

    have "finite (inference_system.inferences_between (ord_FO_\<Gamma> S) (fst ` set_mset Q) C')"
      using finite_ord_FO_resolution_inferences_between by auto
    then have fin: "finite concls"
      unfolding concls_def by auto

    from False have "\<not> n \<le> weight (C, i)"
      by auto
    then have "{(D, ia) \<in> concls. ia \<le> weight (C, i)} = {}"
      unfolding concls_def by auto
    then have "{#(D, ia) \<in># mset_set concls. ia \<le> weight (C, i)#} = {#}"
      using fin filter_mset_empty_if_finite_and_filter_set_empty[of concls] by auto
    then have N_low_weight_empty: "{#(D, ia) \<in># N. ia \<le> weight (C, i)#} = {#}"
      unfolding inference_computation unfolding concls_def by auto
    have "weight (C', i') \<le> weight (C, i)"
      using inference_computation by auto
    then have i'_le_w_Ci: "i' \<le> weight (C, i)"
      using generation_le_weight[of i' C'] by auto

    have subs: "{#(D, ia) \<in># N + {#(D, j) \<in># P. D \<noteq> C'#} + (Q + {#(C', i')#}). ia \<le> weight (C, i)#}
            \<subseteq># {#(D, ia) \<in># {#} + (P + {#(C', i')#}) + Q. ia \<le> weight (C, i)#}"
       using N_low_weight_empty apply auto
       by (simp add: multiset_filter_mono)  

    (* First component *)
    have "fst3 (RP_combined_measure_new (weight (C, i)) St') \<le> fst3 (RP_combined_measure_new (weight (C, i)) St)" 
      unfolding St'_def St_def by auto
    moreover
    (* Second component *)
    have "fst (RP_filtered_measure ((\<lambda>(D, ia). ia \<le> weight (C, i))) St') = 
           (\<Sum>(C, i)\<in>#{#(D, ia) \<in># N + {#(D, j) \<in># P. D \<noteq> C'#} + (Q + {#(C', i')#}). ia \<le> weight (C, i)#}. Suc (size C))"
      unfolding St'_def by auto
    also have "... \<le> (\<Sum>(C, i)\<in>#{#(D, ia) \<in># {#} + (P + {#(C', i')#}) + Q. ia \<le> weight (C, i)#}. Suc (size C))"
      using subs sum_image_mset_mono by blast
    also have "... = fst (RP_filtered_measure ((\<lambda>(D, ia). ia \<le> weight (C, i))) St)"
      unfolding St_def by auto
    finally have "fst (RP_filtered_measure ((\<lambda>(D, ia). ia \<le> weight (C, i))) St') \<le> fst (RP_filtered_measure ((\<lambda>(D, ia). ia \<le> weight (C, i))) St)"
      by auto
    then have "fst3 (snd3 (RP_combined_measure_new (weight (C, i)) St')) \<le> fst3 (snd3 (RP_combined_measure_new (weight (C, i)) St))"
      by auto
    moreover
    have "snd3 (snd3 (RP_combined_measure_new (weight (C, i)) St')) = snd3 (snd3 (RP_combined_measure_new (weight (C, i)) St))"
      unfolding St_def St'_def using N_low_weight_empty by auto
    moreover
    have "trd3 (snd3 (RP_combined_measure_new (weight (C, i)) St')) < trd3 (snd3 (RP_combined_measure_new (weight (C, i)) St))"
      unfolding St_def St'_def using i'_le_w_Ci 
      by (simp add: le_imp_less_Suc multiset_filter_mono size_mset_mono)
    ultimately show ?thesis
      unfolding natLess_def St'_def St_def lex_prod_def by force
  qed
qed

(* FIXME: come up with better name *)
lemma stay_or_delete_completely:
  assumes "St \<leadsto>\<^sub>w St'" "(C,i) \<in># wP_of_wstate St" 
    "\<forall>k. (C, k) \<in># wP_of_wstate St \<longrightarrow> i \<le> k"
  shows "(C, i) \<in># wP_of_wstate St' \<or> (\<forall>j. (C, j) \<notin># wP_of_wstate St')"
using assms proof (induction rule: weighted_RP.induct)
  case (tautology_deletion A C' N i' P Q n)
  then show ?case by auto
next
  case (forward_subsumption D P Q C' N i' n)
  then show ?case by auto
next
  case (backward_subsumption_P D N C' P Q n)
  then show ?case by auto
next
  case (backward_subsumption_Q D N C' P Q i' n)
  then show ?case by auto
next
  case (forward_reduction D L' P Q L \<sigma> C' N i' n)
then show ?case by auto
next
  case (backward_reduction_P D L' N L \<sigma> C' P i' Q n)
  show ?case
  proof (cases "C = C' + {#L#}")
    case True
    note True_outer = this
    then have C_i_in: "(C, i) \<in># P + {#(C, i')#}"
      using backward_reduction_P by auto
    then have max:
      "\<And>k. (C, k) \<in># P + {#(C, i')#} \<Longrightarrow> k \<le> i'"
      using backward_reduction_P unfolding True[symmetric] by auto
    then have "count (P + {#(C, i')#}) (C, i') \<ge> 1"
      by auto
    moreover
    {
      assume asm: "count (P + {#(C, i')#}) (C, i') = 1"
      then have nin_P: "(C, i') \<notin># P"
        using not_in_iff by force       
      have ?thesis
      proof (cases "(C, i) = (C, i')")
        case True
        then have "i = i'"
          by auto
        then have "\<forall>j. (C, j) \<in># P + {#(C, i')#} \<longrightarrow> j = i'"
          using max backward_reduction_P(6) unfolding True_outer[symmetric] by force
        then have "\<forall>j. (C, j) \<notin># P"
          using nin_P by auto
        then have "\<forall>j. (C, j) \<notin># P + {#(C', i')#}"
          using True_outer[symmetric] by auto
        then show ?thesis 
          by auto
      next
        case False
        then have "i \<noteq> i'"
          by auto
        then have "(C, i) \<in># P"
          using C_i_in by auto
        then have "(C, i) \<in># P + {#(C', i')#}"
          by auto
        then show ?thesis
          by auto
      qed
    }
    moreover
    {
      assume "count (P + {#(C, i')#}) (C, i') > 1"
      then have "set_mset (P + {#(C, i')#}) = set_mset P"
        by auto
      then have ?thesis
        using C_i_in by auto
    }
    ultimately show ?thesis
      by (cases "count (P + {#(C, i')#}) (C, i') = 1") auto
  next
    case False
    then show ?thesis
      using backward_reduction_P by auto
  qed
next
  case (backward_reduction_Q D L' N L \<sigma> C' P Q i' n)
  then show ?case by auto
next
  case (clause_processing N C' i' P Q n)
  then show ?case by auto
next
  case (inference_computation P C' i' N n Q)
  then show ?case by auto
qed

(* FIXME: come up with better name *)
lemma stay_or_delete_completely_Sts:
  assumes "enat (Suc k) < llength Sts"
  assumes "(C, i) \<in># wP_of_wstate (lnth Sts k)"
  assumes "\<forall>j. (C, j) \<in># wP_of_wstate (lnth Sts k) \<longrightarrow> i \<le> j"
  shows "(C, i) \<in># wP_of_wstate (lnth Sts (Suc k)) \<or> (\<forall>j. (C, j) \<notin># wP_of_wstate (lnth Sts (Suc k)))"
proof -
  from deriv have "lnth Sts k \<leadsto>\<^sub>w lnth Sts (Suc k)"
    using assms chain_lnth_rel by auto
  then show ?thesis
    using stay_or_delete_completely[of "lnth Sts k" "lnth Sts (Suc k)" C i] assms by metis
qed

lemma in_lnth_in_Supremum_ldrop:
  assumes llength_infty: "llength xs = \<infinity>"
  assumes "x \<in># (lnth xs i)"
  shows "x \<in> Sup_llist (lmap set_mset (ldrop (enat i) xs))"
  by (metis (no_types, lifting) assms(2) contra_subsetD enat.distinct(1) enat_ord_code(4) ldrop_enat 
       ldropn_Suc_conv_ldropn lfinite_ldrop lfinite_lmap llength_eq_infty_conv_lfinite llength_infty 
       lnth_0 lnth_lmap lnth_subset_Sup_llist)

(* FIXME: come up with better name. Or inline the proof. *)
lemma is_least_reformulation:
  assumes 
    "is_least (\<lambda>i. (C, i) \<in> Sup_llist (lmap (set_mset \<circ> wP_of_wstate) (ldrop (enat x) Sts))) j" and
    "llength Sts = \<infinity>"
  shows "\<exists>xb. (\<forall>k xa. (C, k) \<in># wP_of_wstate (lnth (ldrop (enat x) Sts) xa) \<longrightarrow> j \<le> k) \<and>
              (C, j) \<in># wP_of_wstate (lnth (ldrop (enat x) Sts) xb)"
proof -
  from assms obtain xb where "(C, j) \<in> lnth (lmap (set_mset \<circ> wP_of_wstate) (ldrop (enat x) Sts)) xb"
    unfolding is_least_def unfolding Sup_llist_def using assms(2) by blast
  then have "(C, j) \<in># wP_of_wstate (lnth (ldrop (enat x) Sts) xb)"
    using assms(2)
    by (metis (no_types, lifting) comp_apply enat.distinct(2) enat_ord_code(4) lfinite_ldrop llength_eq_infty_conv_lfinite lnth_lmap)
  moreover
  from assms have "\<forall>n'. (C, n') \<in> Sup_llist (lmap (set_mset \<circ> wP_of_wstate) (ldrop (enat x) Sts)) \<longrightarrow> j \<le> n'" 
    using linorder_not_less unfolding is_least_def by auto
  then have "\<forall>n' xa. (C, n') \<in># wP_of_wstate (lnth (ldrop (enat x) Sts) xa) \<longrightarrow> j \<le> n'"
    by (smt assms(2) enat.distinct(2) enat_ord_code(4) lfinite_ldrop llength_eq_infty_conv_lfinite 
         llength_lmap llist.map_comp lnth_lmap lnth_subset_Sup_llist subsetCE)
  ultimately show ?thesis
    by auto
qed

lemma persistent_wclause_in_P_if_persistent_clause_in_P:
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
  have C_in_nth_P: "\<And>xa. C \<in> P_of_state (state_of_wstate (lnth (ldrop x Sts) xa))"
    using x_p(2)[of "x + _"] llength_infty llength_infty by (force simp add: add.commute) 
  have Ci_in_nth_wP: "\<forall>xa. \<exists>i. (C,i) \<in># wP_of_wstate (lnth (ldrop x Sts) xa)"
    apply rule
    subgoal for xa
      using C_in_nth_P[of xa]
      apply (cases "(lnth (ldrop (enat x) Sts)) xa")
      apply auto
      done
    done
  define in_Sup_wP where 
    "in_Sup_wP = (\<lambda>i. (C, i) \<in> Sup_llist (lmap (set_mset \<circ> wP_of_wstate) (ldrop x Sts)))"
  have "in_Sup_wP i"
    unfolding in_Sup_wP_def using i_p assms(1) in_lnth_in_Supremum_ldrop[of "lmap wP_of_wstate Sts" "(C, i)" x]
    by (simp add: llist.map_comp)
  then obtain j where "is_least in_Sup_wP j"
    unfolding in_Sup_wP_def[symmetric] using least_exists by metis
  then have "\<exists>xb. (\<forall>k xa. (C, k) \<in># wP_of_wstate (lnth (ldrop x Sts) xa) \<longrightarrow> j \<le> k)
     \<and> (C,j) \<in># wP_of_wstate (lnth (ldrop x Sts) xb)"
    using assms(1) unfolding in_Sup_wP_def using is_least_reformulation by auto
  then obtain j xb where j_p:
    "\<forall>k xa. (C, k) \<in># wP_of_wstate (lnth (ldrop x Sts) xa) \<longrightarrow> j \<le> k"
    "(C,j) \<in># wP_of_wstate (lnth (ldrop x Sts) xb)"
    by auto
  have Ci_stays: "\<And>xc. (C,j) \<in># wP_of_wstate (lnth (ldrop (x+xb) Sts) xc)"
    subgoal for xc
    proof (induction xc)
      case 0
      then show ?case
        using j_p lnth_ldrop[of 0 _ Sts] llength_infty
        by (simp add: add.commute) 
    next
      case (Suc xc)
      have any_Ck_in_wP: "\<forall>k. (C, k) \<in># wP_of_wstate (lnth Sts (x + xb + xc)) \<longrightarrow> j \<le> k"
      proof (rule, rule)
        fix k :: nat
        assume "(C, k) \<in># wP_of_wstate (lnth Sts (x + xb + xc))"
        then have "(C, k) \<in># wP_of_wstate (lnth (ldrop (enat x) Sts) (xb + xc))"
          by (simp add: add.commute add.left_commute llength_infty)
        then show "j \<le> k" 
          using j_p(1) by auto
      qed
      from Suc have "(C, j) \<in># wP_of_wstate (lnth (ldrop (x+xb) Sts) xc)"
        by blast
      then have Cj_in_wP: "(C, j) \<in># wP_of_wstate (lnth Sts ((x+xb) + xc))"
        by (simp add: add.commute llength_infty)
      moreover have "C \<in> P_of_state (state_of_wstate (lnth Sts (Suc (x + xb + xc))))"
        using x_p(2) by (auto simp add: llength_infty)
      then have "\<exists>k. (C, k) \<in># wP_of_wstate (lnth Sts (Suc (x + xb + xc)))"
        by (smt Ci_in_nth_wP add.commute add.left_commute add_Suc_right enat_ord_code(4) ldrop_enat llength_infty lnth_ldropn)
      ultimately have "(C, j) \<in># wP_of_wstate (lnth Sts (Suc (x + xb + xc)))"
        using stay_or_delete_completely_Sts[of "x + xb + xc" C j, OF _ Cj_in_wP any_Ck_in_wP] 
        by (auto simp add: llength_infty)
      then have "(C, j) \<in># lnth (lmap wP_of_wstate Sts) (Suc ((x+xb) + xc))"
        by (simp add: llength_infty)
      then show ?case using llength_infty by (simp add: add.commute)
    qed
    done
  have "(\<And>xa. x+xb \<le> xa \<Longrightarrow> (C, j) \<in># wP_of_wstate (lnth Sts xa))"
  proof -
    fix xa :: nat
    assume a:
      "x+xb \<le> xa"
    have "(C, j) \<in># wP_of_wstate (lnth (ldrop (enat (x + xb)) Sts) (xa - (x+xb)))"
      using Ci_stays[of "xa - (x+xb)"] by auto
    then show "(C, j) \<in># wP_of_wstate (lnth Sts xa)"
      using lnth_ldrop[of "x + xb" "xa - x" Sts] a by (simp add: llength_infty) 
  qed
  then have "(C, j) \<in> Liminf_llist (lmap (set_mset \<circ> wP_of_wstate) Sts)"
    unfolding Liminf_llist_def by (auto simp add: llength_infty)
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
      unfolding P_def by (cases "llast Sts") auto
    then have "weight (D, j) \<in> weight ` set_mset P"
       by auto
    then have "\<exists>w. is_least (\<lambda>w. w \<in> (weight ` set_mset P)) w"
      using least_exists by auto
    then have "\<exists>D j. (\<forall>(D', j') \<in># P. weight (D, j) \<le> weight (D', j')) \<and> (D, j) \<in># P"
      using assms linorder_not_less unfolding is_least_def by (auto 6 0)
    then obtain D j where min: "(\<forall>(D', j') \<in># P. weight (D, j) \<le> weight (D', j'))"
      and Dj_in_p: "(D, j) \<in># P"
      by auto
    from min have min: "(\<forall>(D', j') \<in># P - {#(D, j)#}. weight (D, j) \<le> weight (D', j'))"
        using mset_subset_diff_self[OF Dj_in_p] by auto
    define N' where "N' = mset_set ((\<lambda>D'. (D', n)) ` concls_of (inference_system.inferences_between (ord_FO_\<Gamma> S) (set_mset (image_mset fst Q)) D))"
    have "llast Sts \<leadsto>\<^sub>w (N', {#(D', j') \<in># P - {# (D, j) #}. D' \<noteq> D#}, Q + {#(D,j)#}, Suc n)"
      using weighted_RP.inference_computation[of "P - {#(D, j)#}" D j N' n Q, OF min N'_def]
      using of_wstate_split[symmetric, of "llast Sts"]
      unfolding N_def[symmetric] P_def[symmetric] Q_def[symmetric] n_def[symmetric]
      unfolding b
      using Dj_in_p by auto
    then have "\<exists>St'. llast Sts \<leadsto>\<^sub>w St'"
      by auto
  }
  ultimately have "\<exists>St'. llast Sts \<leadsto>\<^sub>w St'"
     by auto
   then show False
     using no_inf_from_last by metis
 qed

lemma ldrop_Suc_conv_ltl: "ldrop (enat (Suc k)) xs = ltl (ldrop (enat k) xs)"
  by (metis eSuc_enat ldrop_eSuc_conv_ltl) 

lemma lhd_ldrop':
  assumes "enat k < llength xs"
  shows "lhd (ldrop (enat k) xs) = lnth xs k"
  using assms
  by (simp add: lhd_ldrop)  

lemma inf_chain_ltl_chain:
  assumes 
    "chain R xs" and
    "llength xs = \<infinity>"
  shows "chain R (ltl xs)"
proof -
  from assms have "\<exists>xsa x. xs = LCons x xsa \<and> chain R xsa \<and> R x (lhd xsa)"
    using chain.simps[of R xs]
    by (meson lfinite_LConsI lfinite_code(1) llength_eq_infty_conv_lfinite) 
  then show ?thesis
    by auto
qed

lemma inf_chain_ldrop_chain:
  assumes 
    "chain R xs" and
    "\<not> lfinite xs"
  shows "chain R (ldrop (enat k) xs)"
proof (induction k)
  case 0
  then show ?case
    using ldrop_0 zero_enat_def assms by auto
next
  case (Suc k)
  have "llength (ldrop (enat k) xs) = \<infinity>"
    using assms 
    by (simp add: not_lfinite_llength) 
  with Suc have "chain R (ltl (ldrop (enat k) xs))"
    using inf_chain_ltl_chain[of R "(ldrop (enat k) xs)"] by auto
  then show ?case
    using ldrop_Suc_conv_ltl[of k xs] by auto
qed

lemma N_of_state_state_of_wstate_wN_of_wstate:
  assumes "C \<in> N_of_state (state_of_wstate St)"
  shows "\<exists>i. (C, i) \<in># wN_of_wstate St"
  by (smt N_of_state.elims assms eq_fst_iff fstI fst_conv image_iff of_wstate_split set_image_mset 
       state_of_wstate.simps)

lemma in_wN_of_wstate_in_N_of_wstate:
  assumes "(C, i) \<in># wN_of_wstate St"
  shows "C \<in> N_of_wstate St"
  using assms by (metis (mono_tags, lifting) N_of_state.simps comp_apply fst_conv image_eqI 
                   of_wstate_split set_image_mset state_of_wstate.simps)

lemma in_wP_of_wstate_in_P_of_wstate:
  assumes "(C, i) \<in># wP_of_wstate St"
  shows "C \<in> P_of_wstate St"
  using assms by (metis (mono_tags, lifting) P_of_state.simps comp_apply fst_conv image_eqI 
                   of_wstate_split set_image_mset state_of_wstate.simps)

lemma in_wQ_of_wstate_in_Q_of_wstate:
  assumes "(C, i) \<in># wQ_of_wstate St"
  shows "C \<in> Q_of_wstate St"
  using assms by (metis (mono_tags, lifting) Q_of_state.simps comp_apply fst_conv image_eqI 
                   of_wstate_split set_image_mset state_of_wstate.simps)

lemma n_of_wstate_weighted_RP_increasing:
  assumes "St \<leadsto>\<^sub>w St'"
  shows "n_of_wstate St \<le> n_of_wstate St'"
  using assms
  by (induction rule: weighted_RP.induct) auto

lemma nth_of_wstate_monotonic:
  assumes "j < llength Sts"
  assumes "i \<le> j"
  shows "n_of_wstate (lnth Sts i) \<le> n_of_wstate (lnth Sts j)"
using assms proof (induction "j-i" arbitrary: i)
  case 0
  then have "j = i" by auto
  then show ?case by force
next
  case (Suc x)
  then have "x = j - (i + 1)"
    by auto
  then have "n_of_wstate (lnth Sts (i + 1)) \<le> n_of_wstate (lnth Sts j)"
    using Suc by auto
  moreover 
  have "i < j"
    using Suc by auto
  then have "Suc i < llength Sts"
    using Suc
    by (metis enat_ord_simps(2) le_less_Suc_eq less_le_trans not_le) 
  then have "lnth Sts i \<leadsto>\<^sub>w lnth Sts (Suc i)"
    using deriv chain_lnth_rel[of "op \<leadsto>\<^sub>w" Sts i] by auto
  then have "n_of_wstate (lnth Sts i) \<le> n_of_wstate (lnth Sts (i + 1))"
    using n_of_wstate_weighted_RP_increasing[of "lnth Sts i" "lnth Sts (i + 1)"] by auto
  ultimately show ?case
    by auto
qed

(* 
FIXME:
  1. Prove with lnth_rel_chain
  2. Generalize this to any measure and relation that fit together
  3. Use the generalized in both cases of weighted_RP_fair
*)
lemma infinite_chain_relation_measure:
  assumes 
    non_infer_chain: "chain op \<leadsto>\<^sub>w\<^sub>n\<^sub>i (ldrop (enat k) Sts)" and
    inf:"llength Sts = \<infinity>"
  shows "chain (\<lambda>x y. (x, y) \<in> RP_filtered_relation_new)\<inverse>\<inverse> (lmap (RP_filtered_measure (\<lambda>Ci. True)) (ldrop (enat k) Sts))"
using non_infer_chain proof (coinduction arbitrary: k rule: chain.coinduct)
  case chain
  from inf have inff: "\<not> lfinite Sts"
    using llength_eq_infty_conv_lfinite by blast 
  from inf have k_lt_len: "enat k < llength Sts"
    by auto
  define x where "x = (RP_filtered_measure (\<lambda>Ci. True)) (lnth Sts k)"
  define xs where "xs = lmap (RP_filtered_measure (\<lambda>Ci. True)) (ldrop (enat (Suc k)) Sts)"
  have "(ldrop (enat k) Sts) = LCons ((lhd (ldrop (enat k) Sts))) ((ltl (ldrop (enat k) Sts)))"
    using chain(1) inff
    unfolding ldrop_Suc_conv_ltl
    unfolding lhd_ldrop'[symmetric, OF k_lt_len]
    by (metis enat.distinct(1) lfinite_LNil lfinite_ldrop llist.exhaust_sel)
  then have "lmap (RP_filtered_measure (\<lambda>Ci. True)) (ldrop (enat k) Sts) = LCons x xs"        
    unfolding x_def xs_def using chain
    by (metis (no_types, lifting) k_lt_len ldrop_Suc_conv_ltl lhd_ldrop' llist.simps(13)) 
  moreover
  have "chain op \<leadsto>\<^sub>w\<^sub>n\<^sub>i (ldrop (enat (Suc k)) Sts)"
    using chain inff
    unfolding ldrop_Suc_conv_ltl
    using inf_chain_ltl_chain[of "op \<leadsto>\<^sub>w\<^sub>n\<^sub>i" "(ldrop (enat k) Sts)"]
    by (simp add: not_lfinite_llength)
  moreover
  have "lnth (ldrop (enat k) Sts) 0 \<leadsto>\<^sub>w\<^sub>n\<^sub>i lnth (ldrop (enat k) Sts) (Suc 0)"
    using chain chain_lnth_rel[of "op \<leadsto>\<^sub>w\<^sub>n\<^sub>i" "(ldrop (enat k) Sts)" 0] inf
    by (metis enat.distinct(2) enat_ord_code(4) lfinite_ldrop llength_eq_infty_conv_lfinite)
  then have "lnth Sts k \<leadsto>\<^sub>w\<^sub>n\<^sub>i lnth Sts (Suc k)"
    using lnth_ldrop[of k 0 Sts] lnth_ldrop[of k "Suc 0" Sts]
    by (simp add: inf)
  then have "((RP_filtered_measure (\<lambda>Ci. True)) (lnth Sts (Suc k)), (RP_filtered_measure (\<lambda>Ci. True)) (lnth Sts k)) \<in> RP_filtered_relation_new"
    using weighted_RP_Non_Inference_measure_decreasing[of "lnth Sts k" "lnth Sts (Suc k)"] by auto
  then have "(lhd xs, x) \<in> RP_filtered_relation_new"
    unfolding xs_def x_def
    by (simp add: inf lhd_ldrop')
  then have "(\<lambda>x y. (x, y) \<in> RP_filtered_relation_new)\<inverse>\<inverse> x (lhd xs)"
    by auto
  ultimately show ?case
    using xs_def by auto
qed

theorem weighted_RP_fair: "fair_state_seq (lmap state_of_wstate Sts)" (* Proof using the simpler measure *)
proof (rule ccontr)
  assume asm: "\<not> fair_state_seq (lmap state_of_wstate Sts)"
  then have inff: "\<not> lfinite Sts" using infinite_if_not_fair
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
      (* You need a persistent_wclause_if_persistent_clause for N.
         No. You don't need that. The following arguments should work even when the
         numbers change! *)
    then obtain x where "enat x < llength Sts"
      "\<forall>xa. x \<le> xa \<and> enat xa < llength Sts \<longrightarrow> C \<in> N_of_state (state_of_wstate (lnth Sts xa))"
      unfolding Liminf_llist_def by auto
    then have "\<exists>k. \<forall>j. k \<le> j \<longrightarrow> (\<exists>i. (C, i) \<in># wN_of_wstate (lnth Sts j))"
      unfolding Liminf_llist_def by (force simp add: inf N_of_state_state_of_wstate_wN_of_wstate)
    then obtain k where k_p: 
      "\<And>j. k \<le> j \<Longrightarrow> \<exists>i. (C, i) \<in># wN_of_wstate (lnth Sts j)"
      unfolding Liminf_llist_def 
      by auto
    have chain_drop_Sts: "chain op \<leadsto>\<^sub>w (ldrop k Sts)"
      using deriv inf inff inf_chain_ldrop_chain by auto
    have in_N_j: "\<And>j. \<exists>i. (C, i) \<in># wN_of_wstate (lnth (ldrop k Sts) j)"
      using k_p by (simp add: add.commute inf)
    (* ultimately *)
    have "chain op \<leadsto>\<^sub>w\<^sub>n\<^sub>i (ldrop k Sts)"
    proof (rule lnth_rel_chain)
      show "\<not> lnull (ldrop (enat k) Sts)"
        by (simp add: inf inff)
    next
      show "\<forall>j. enat (j + 1) < llength (ldrop (enat k) Sts) \<longrightarrow>
            lnth (ldrop (enat k) Sts) j \<leadsto>\<^sub>w\<^sub>n\<^sub>i lnth (ldrop (enat k) Sts) (j + 1)"
      proof (rule, rule)
        fix j :: nat
        assume "enat (j + 1) < llength (ldrop (enat k) Sts)"
        then have "lnth (ldrop (enat k) Sts) j \<leadsto>\<^sub>w lnth (ldrop (enat k) Sts) (j + 1)"
          using chain_lnth_rel[OF chain_drop_Sts, of j] by auto
        moreover have "N_of_wstate (lnth (ldrop (enat k) Sts) j) \<noteq> {}"
          using in_N_j[of j] in_wN_of_wstate_in_N_of_wstate[of C _ "lnth (ldrop (enat k) Sts) j"]
          by auto
        ultimately show "lnth (ldrop (enat k) Sts) j \<leadsto>\<^sub>w\<^sub>n\<^sub>i lnth (ldrop (enat k) Sts) (j + 1)"
          unfolding weighted_RP_Non_Inference_def by auto
      qed
    qed
    then have "chain (\<lambda>x y. (x, y) \<in> RP_filtered_relation_new)\<inverse>\<inverse> (lmap (RP_filtered_measure (\<lambda>Ci. True)) (ldrop k Sts))"
      using inff inf infinite_chain_relation_measure by auto
    then show False
      using wfP_iff_no_infinite_down_chain_llist[of "\<lambda>x y. (x, y) \<in> RP_filtered_relation_new"] 
        wf_RP_filtered_relation inff
      by (metis (no_types, lifting) inf_llist_lnth ldrop_enat_inf_llist lfinite_inf_llist 
        lfinite_lmap wfPUNIVI wf_induct_rule)
  next
    assume asm: "C \<in> Liminf_llist (lmap P_of_state (lmap state_of_wstate Sts))"
    from asm obtain i where i_p:
      "enat i < llength Sts"
      "\<And>j. i \<le> j \<and> enat j < llength Sts \<Longrightarrow> C \<in> P_of_state (state_of_wstate (lnth Sts j))"
      unfolding Liminf_llist_def by auto
    then obtain i where "(C, i) \<in> Liminf_llist (lmap (set_mset \<circ> wP_of_wstate) Sts)"
      using persistent_wclause_in_P_if_persistent_clause_in_P[of C] using asm inf by auto
    then have stay: "\<exists>l. \<forall>k\<ge>l. (C, i) \<in> (set_mset \<circ> wP_of_wstate) (lnth Sts k)"
      unfolding Liminf_llist_def using inff inf by auto
    then obtain k where k_p:
      "(\<forall>k'\<ge>k. (C, i) \<in> (set_mset \<circ> wP_of_wstate) (lnth Sts k'))"
      by blast
    have Ci_in: "\<forall>k'. (C, i) \<in> (set_mset \<circ> wP_of_wstate) (lnth (ldrop k Sts) k')"
      using k_p
      using lnth_ldrop[of k _ Sts]
      using inf inff by force
    then have Ci_inn: "\<forall>k'. (C, i) \<in># (wP_of_wstate) (lnth (ldrop k Sts) k')"
      by auto
    have "chain op \<leadsto>\<^sub>w (ldrop k Sts)"
      using deriv 
      using inf_chain_ldrop_chain inf inff
      by auto
    then have "chain (\<lambda>x y. (x, y) \<in> RP_combined_relation_new)\<inverse>\<inverse> (lmap (RP_combined_measure_new (weight (C, i))) (ldrop k Sts))"
      using inff inf Ci_in
    proof (coinduction arbitrary: k rule: chain.coinduct)
      case chain (* FIXME: Some copy paste from above. *)
      then have k_lt_len: "enat k < llength Sts"
        by auto
      have chain_6: "\<And>k'. (C, i) \<in># wP_of_wstate (lnth (ldrop (enat k) Sts) k')"
        using chain by auto
      define x where "x = RP_combined_measure_new (weight (C, i)) (lnth Sts k)"
      define xs where "xs = lmap (RP_combined_measure_new (weight (C, i))) (ldrop (enat (Suc k)) Sts)"
      have f: "(ldrop (enat k) Sts) = LCons ((lhd (ldrop (enat k) Sts))) ((ltl (ldrop (enat k) Sts)))"
        using chain
        unfolding ldrop_Suc_conv_ltl
        unfolding lhd_ldrop'[symmetric, OF k_lt_len]
        by (metis enat.distinct(1) lfinite_LNil lfinite_ldrop llist.exhaust_sel)
      then have "lmap (RP_combined_measure_new (weight (C, i))) (ldrop (enat k) Sts) = LCons x xs"        
        unfolding x_def xs_def using chain
        by (metis (no_types, lifting) k_lt_len ldrop_Suc_conv_ltl lhd_ldrop' llist.simps(13)) 
      moreover
      have "chain op \<leadsto>\<^sub>w (ldrop (enat (Suc k)) Sts)"
        using chain
        unfolding ldrop_Suc_conv_ltl
        using inf_chain_ltl_chain[of "op \<leadsto>\<^sub>w" "(ldrop (enat k) Sts)"]
        by (simp add: not_lfinite_llength)
      moreover
      have "lnth (ldrop (enat k) Sts) 0 \<leadsto>\<^sub>w lnth (ldrop (enat k) Sts) (Suc 0)"
        using chain chain_lnth_rel[of "op \<leadsto>\<^sub>w" "(ldrop (enat k) Sts)" 0]
        by (metis enat.distinct(2) enat_ord_code(4) lfinite_ldrop llength_eq_infty_conv_lfinite)
      then have "lnth Sts k \<leadsto>\<^sub>w lnth Sts (Suc k)"
        using lnth_ldrop[of k 0 Sts] lnth_ldrop[of k "Suc 0" Sts]
        by (simp add: inf)
      then have "(RP_combined_measure_new (weight (C, i)) (lnth Sts (Suc k)), RP_combined_measure_new (weight (C, i)) (lnth Sts k)) \<in> RP_combined_relation_new"
        using weighted_RP_Inference_has_measure2[of "lnth Sts k" "lnth Sts (Suc k)" C i]
          using chain_6[of 0] k_lt_len by auto 
      then have "(lhd xs, x) \<in> RP_combined_relation_new"
        unfolding xs_def x_def
        by (simp add: inf lhd_ldrop')
      then have "(\<lambda>x y. (x, y) \<in> RP_combined_relation_new)\<inverse>\<inverse> x (lhd xs)"
        by auto
      
      note lol = calculation this
      show ?case
        apply (rule disjI2)
        apply (rule_tac x=xs in exI)
        apply (rule_tac x=x in exI)
        apply (rule conjI)
        subgoal
          using chain xs_def x_def lol by auto
        subgoal
          apply (rule conjI)
          subgoal
            apply (rule disjI1)
            apply (rule_tac x="(Suc k)" in exI)
            apply (rule conjI)
            subgoal
              using xs_def .
            subgoal
              apply (rule conjI)
              subgoal
                by (simp add: lol(2))
              subgoal
                apply (rule conjI)
                subgoal 
                  using inf inff by auto
                subgoal
                  apply (rule conjI)
                  subgoal
                    using inf inff by auto
                  subgoal
                    apply (rule allI)
                    subgoal for k'
                      using chain_6[of "Suc k'"] inf inff 
                      apply auto
                      done
                    done
                  done
                done
              done
            done
          subgoal
            using chain xs_def x_def lol by auto
          done
        done
    qed
    then show False
      using wfP_iff_no_infinite_down_chain_llist[of "\<lambda>x y. (x, y) \<in> RP_combined_relation_new"] 
        wf_RP_combined_relation_new inff
      by (metis (no_types, lifting) inf_llist_lnth ldrop_enat_inf_llist lfinite_inf_llist 
        lfinite_lmap wfPUNIVI wf_induct_rule)
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
