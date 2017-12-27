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

definition weighted_RP_Non_Inference :: "'a wstate \<Rightarrow> 'a wstate \<Rightarrow> bool" (infix "\<leadsto>\<^sub>w\<^sub>n\<^sub>i" 50) where
  "St \<leadsto>\<^sub>w\<^sub>n\<^sub>i St' \<longleftrightarrow> St \<leadsto>\<^sub>w St' \<and> N_of_wstate St \<noteq> {}"

definition weighted_RP_Inference :: "'a wstate \<Rightarrow> 'a wstate \<Rightarrow> bool" (infix "\<leadsto>\<^sub>w\<^sub>i" 50) where
  "St \<leadsto>\<^sub>w\<^sub>i St' \<longleftrightarrow> St \<leadsto>\<^sub>w St' \<and> N_of_wstate St = {}"

(* FIXME: Come up with a better name *)
lemma weighted_RP_split: "St \<leadsto>\<^sub>w St' \<longleftrightarrow> St \<leadsto>\<^sub>w\<^sub>i St' \<or> St \<leadsto>\<^sub>w\<^sub>n\<^sub>i St'"
  unfolding weighted_RP_Non_Inference_def weighted_RP_Inference_def by auto

find_theorems inf_llist LCons

(* FIXME: better name *)
lemma a:
  assumes "\<forall>i. (f (Suc i), f i) \<in> {(x, y). r x y}"
  shows "\<not> lfinite (inf_llist f) \<and> chain r\<inverse>\<inverse> (inf_llist f)"
proof
  show inf: "\<not> lfinite (inf_llist f)"
    using assms by auto
  from assms inf
  show "chain r\<inverse>\<inverse> (inf_llist f)"
  proof (coinduction arbitrary: f rule: chain.coinduct)
    case chain
    have "inf_llist f = LCons (f 0) (inf_llist (f \<circ> Suc))"
      using inf_llist_rec unfolding comp_def by metis
    moreover 
    from chain have "(\<forall>i. (f (Suc i), f i) \<in> {(x, y). r x y}) \<or> chain r\<inverse>\<inverse> (inf_llist (f \<circ> Suc))"
      by auto
    moreover have "r\<inverse>\<inverse> (f 0) (f 1)"
      using chain by auto
    then have "r\<inverse>\<inverse> (f 0) (lhd (inf_llist (f o Suc)))"
      using chain by simp 
    ultimately show ?case
      by auto
  qed
qed

(* FIXME: better name *)
lemma b: 
  assumes "\<not> lfinite c"
  assumes "chain r\<inverse>\<inverse> c"
  shows "(lnth c (Suc i), lnth c i) \<in> {(x, y). r x y}"
  using assms chain_lnth_rel[of "r\<inverse>\<inverse>" c i]
  by (simp add: lfinite_conv_llength_enat)

(* FIXME: better name *)
lemma c: "(\<exists>f. \<forall>i. (f (Suc i), f i) \<in> {(x, y). r x y}) \<longleftrightarrow> (\<exists>c. \<not> lfinite c \<and> chain r\<inverse>\<inverse> c)"
  using a b by blast

lemma wfP_iff_no_infinite_down_chain: "wfP r \<longleftrightarrow> (\<nexists>c. \<not>lfinite c \<and> chain r\<inverse>\<inverse> c)"
proof -
  have "wfP r \<longleftrightarrow>  wf {(x, y). r x y}"
    unfolding wfP_def by auto
  also have "... \<longleftrightarrow> (\<nexists>f. \<forall>i. (f (Suc i), f i) \<in> {(x, y). r x y})"
    unfolding wf_iff_no_infinite_down_chain by auto
  also have "... \<longleftrightarrow> (\<nexists>c. \<not>lfinite c \<and> chain r\<inverse>\<inverse> c)"
    using c by metis
  finally show ?thesis 
    by auto
qed

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

abbreviation RP_Non_Inference_measure :: "'a wstate \<Rightarrow> _" where
  "RP_Non_Inference_measure \<equiv> (\<lambda>(N, P, Q, n). 
                              (sum_mset (image_mset (\<lambda>(C, i). Suc (size C)) (N + P + Q)), size N))"

abbreviation RP_relation where
  "RP_relation \<equiv> mult natLess <*lex*> natLess <*lex*> natLess"

abbreviation RP_relation2 where
  "RP_relation2 \<equiv> mult (natLess <*lex*> natLess) <*lex*> natLess"

abbreviation RP_Non_Inference_relation where
  "RP_Non_Inference_relation \<equiv> natLess <*lex*> natLess"

term "((RP_measure max_gen St),(RP_measure max_gen St2)) \<in> RP_relation"
term "((RP_measure2 max_gen St),(RP_measure2 max_gen St)) \<in> RP_relation2"
term "((RP_Non_Inference_measure St),(RP_Non_Inference_measure St)) \<in> RP_Non_Inference_relation"

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

lemma wf_RP_Non_Inference_relation: "wf RP_Non_Inference_relation"
  using wf_natLess wf_mult by auto

lemma weighted_RP_if_weighted_RP_Non_Inference: "St \<leadsto>\<^sub>w\<^sub>n\<^sub>i St' \<Longrightarrow> St \<leadsto>\<^sub>w St'"
  unfolding weighted_RP_Non_Inference_def by auto

(* FIXME: better name *)
lemma multiset_sum_monotone_f:
  assumes "CC \<subset># DD"
  shows "(\<Sum>C\<in>#CC. Suc (f C)) < (\<Sum>C\<in>#DD. Suc (f C))"
  using assms
proof (induction CC arbitrary: DD)
  case empty
  then obtain D where "D\<in>#DD"
    by force
  then have "DD = DD - {# D #} + {# D #}"
    by auto
  then have "(\<Sum>C\<in>#DD. 1) = (\<Sum>C\<in>#DD - {# D #} + {# D #}. 1)"
    by auto
  also have "... = (\<Sum>C\<in>#DD - {# D #}. 1) + (\<Sum>C\<in>#{# D #}. 1)"
    by (metis image_mset_union sum_mset.union)
  also have "... = (\<Sum>C\<in>#DD - {# D #}. 1) + 1"
    by auto
  also have "... > (0 :: nat)"
    by auto
  finally have "(0 :: nat) < (\<Sum>C\<in>#DD. 1)"
    by auto
  then have "0 < (\<Sum>C\<in>#DD. Suc (f C))"
    using gr_zeroI by fastforce
  then show ?case 
    using empty by auto
next
  case (add D CC)
  from this(2) have "(\<Sum>C\<in>#CC. Suc (f C)) < (\<Sum>C\<in>#DD - {#D#}. Suc (f C))"
    using add(1)[of "DD - {#D#}"]
    by (simp add: insert_union_subset_iff)
  then show ?case
    by (smt Suc_le_eq add.prems add_Suc_right add_le_cancel_left insert_DiffM mset_subset_insertD sum_mset.insert)
qed

lemma multiset_sum_monotone_f':
  assumes "CC \<subset># DD"
  shows "(\<Sum>(C,i)\<in>#CC. Suc (f C)) < (\<Sum>(C,i)\<in>#DD. Suc (f C))"
  using assms
multiset_sum_monotone_f[OF assms, of "f o fst"]
  by (metis (mono_tags, lifting) comp_apply image_mset_cong2 split_beta)

(* FIXME: better name *)
lemma remove_strict_subset:
  assumes "C' \<in># CC"
  assumes "p C'"
  shows "{#E \<in># CC. \<not>p E#} \<subset># CC"
proof -
  have subseteq: "{#E \<in># CC. \<not>p E#} \<subseteq># CC"
    by auto

  have "count {#E \<in># CC. \<not>p E#} C' = 0"
    using assms by auto
  moreover
  have "0 < count CC C'"
    using assms by auto
  ultimately have lt_count: "count {#E \<in># CC. \<not>p E#} C' < count CC C'"
    by auto
  
  from subseteq lt_count show ?thesis
    by (metis less_not_refl2 subset_mset.le_neq_trans)  
qed

(* FIXME: better name *)
lemma weighted_RP_Non_Inference_has_measure:
  assumes "St \<leadsto>\<^sub>w\<^sub>n\<^sub>i St'"
  shows "(RP_Non_Inference_measure St', RP_Non_Inference_measure St) \<in> RP_Non_Inference_relation"
  using weighted_RP_if_weighted_RP_Non_Inference[OF assms(1)] using assms proof (induction rule: weighted_RP.induct)
  case (tautology_deletion A C' N i' P Q n)
  then show ?case
    unfolding lex_prod_def natLess_def by auto
next
  case (forward_subsumption D P Q C' N i' n)
  then show ?case
    unfolding lex_prod_def natLess_def by auto
next
  case (backward_subsumption_P D N C' P Q n)
  then obtain i' where  "(C',i') \<in># P"
    by auto
  then have "{#(E, k) \<in># P. E \<noteq> C'#} \<subset># P"
    using remove_strict_subset[of "(C', i')" P "\<lambda>X. fst X =  C'"]
    by (metis (mono_tags, lifting) filter_mset_cong fst_conv prod.case_eq_if)
  then have "(\<Sum>(C, i)\<in>#{#(E, k) \<in># P. E \<noteq> C'#}. Suc (size C)) < (\<Sum>(C, i)\<in>#P. Suc (size C))"
    using multiset_sum_monotone_f'[of "{#(E, k) \<in># P. E \<noteq> C'#}" P size] by metis
  then have "fst (RP_Non_Inference_measure (N, {#(E, k) \<in># P. E \<noteq> C'#}, Q, n)) < fst (RP_Non_Inference_measure (N, P, Q, n))"
    by simp
  then show ?case
   unfolding lex_prod_def natLess_def by auto
next
  case (backward_subsumption_Q D N C' P Q i' n)
  then show ?case
    unfolding lex_prod_def natLess_def by auto
next
  case (forward_reduction D L' P Q L \<sigma> C' N i n)
  then show ?case
    unfolding lex_prod_def natLess_def by auto
next
  case (backward_reduction_P D L' N L \<sigma> C' P i Q n)
  then show ?case
    unfolding lex_prod_def natLess_def by auto
next
  case (backward_reduction_Q D L' N L \<sigma> C' P Q i n)
  then show ?case
    unfolding lex_prod_def natLess_def by auto
next
  case (clause_processing N C' i P Q n)
  then show ?case
    unfolding lex_prod_def natLess_def by auto
next
  case (inference_computation P C' i N n Q)
  then show ?case
    unfolding weighted_RP_Non_Inference_def by auto
qed


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
    proof (cases "C \<in># image_mset fst P")
      case True
      then obtain k where k_p: "(C, k) \<in># P"
        using image_iff by auto
      then have k_i': "k \<le> i'"
        using backward_reduction_P unfolding True_outer by auto
      have "(C, i) \<in># P + {#(C' + {#L#}, i')#}"
        using backward_reduction_P True_outer by auto
      then have "\<exists>j\<le>i. (C, j) \<in># P + {#(C', i')#}"
        using k_p k_i' by auto 
      then have "\<exists>j\<le>i. (C, j) \<in># wP_of_wstate (N, P + {#(C', i')#}, Q, n)"
        by auto
      then show ?thesis
        by auto
    next
      case False
      then have "\<forall>j. (C, j) \<notin># P"
        using image_iff by fastforce
      then have "\<forall>j. (C, j) \<notin># P + {#(C', i')#}"
        using True_outer by auto
      then have "\<forall>j. (C, j) \<notin># wP_of_wstate (N, P + {#(C', i')#}, Q, n)"
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

(* FIXME: Horrible name *)
lemma stay_or_delete_completely_STRONGER':
  assumes "St \<leadsto>\<^sub>w St'" "(C,i) \<in># wP_of_wstate St" 
    "\<forall>k. (C, k) \<in># wP_of_wstate St \<longrightarrow> i \<le> k"
  shows "((C, i) \<in># wP_of_wstate St') \<or> (\<forall>j. (C, j) \<notin># wP_of_wstate St')"
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

(* FIXME: Horrible name *)
lemma stay_or_delete_completely_STRONGER: (* This is only true for full derivations. *)
  assumes "enat (Suc k) < llength Sts"
  assumes a: "(C, i) \<in># wP_of_wstate (lnth Sts k)"
  assumes b: "\<forall>j. (C, j) \<in># wP_of_wstate (lnth Sts k) \<longrightarrow> i \<le> j"
  shows "(C, i) \<in># wP_of_wstate (lnth Sts (Suc k)) \<or> (\<forall>j. (C, j) \<notin># wP_of_wstate (lnth Sts (Suc k)))"
proof -
  from deriv have gg: "lnth Sts k \<leadsto>\<^sub>w lnth Sts (Suc k)"
    using assms chain_lnth_rel by auto
  show ?thesis
    using stay_or_delete_completely_STRONGER'[of "lnth Sts k" "lnth Sts (Suc k)" C i, OF gg a b] by metis
qed

(* FIXME: come up with better name *)
lemma Supremum_drop_and_more:
  assumes llength_infty: "llength Sts = \<infinity>"
  assumes "(C, i) \<in># wP_of_wstate (lnth Sts x)"
  shows "(C, i) \<in> Sup_llist (lmap (set_mset \<circ> wP_of_wstate) (ldrop (enat x) Sts))"
proof -
  from assms have "(C, i) \<in># (wP_of_wstate (lnth ((ldrop (enat x) Sts)) 0))"
    by auto
  then have "(C, i) \<in> (set_mset \<circ> wP_of_wstate) (lnth ((ldrop (enat x) Sts)) 0)"
    by auto
  then have "(C, i) \<in> lnth (lmap (set_mset \<circ> wP_of_wstate) (ldrop (enat x) Sts)) 0"
    by (metis enat.distinct(2) enat_ord_code(4) lfinite_ldrop llength_eq_infty_conv_lfinite llength_infty lnth_lmap)
  moreover
  have "0 < llength (lmap (set_mset \<circ> wP_of_wstate) (ldrop (enat x) Sts))"
    using llength_infty
    by simp
  ultimately show ?thesis
    unfolding Sup_llist_def
    by (metis (no_types, lifting) UN_iff mem_Collect_eq zero_enat_def) 
qed

(* FIXME: come up with better name *)
lemma is_least_reformulation:
  assumes 
    "is_least (\<lambda>i. (C, i) \<in> Sup_llist (lmap (set_mset \<circ> wP_of_wstate) (ldrop (enat x) Sts))) j" and
    "llength Sts = \<infinity>"
  shows "\<exists>xb. (\<forall>k xa. (C, k) \<in># wP_of_wstate (lnth (ldrop (enat x) Sts) xa) \<longrightarrow> j \<le> k) \<and>
              (C, j) \<in># wP_of_wstate (lnth (ldrop (enat x) Sts) xb)"
proof -
  from assms have "(C, j) \<in> Sup_llist (lmap (set_mset \<circ> wP_of_wstate) (ldrop (enat x) Sts))" 
    unfolding is_least_def by auto
  then have "\<exists>xb. (C, j) \<in> lnth (lmap (set_mset \<circ> wP_of_wstate) (ldrop (enat x) Sts)) xb"
    unfolding Sup_llist_def using assms(2) by blast
  then obtain xb where "(C, j) \<in> lnth (lmap (set_mset \<circ> wP_of_wstate) (ldrop (enat x) Sts)) xb"
    by auto
  then have "(C, j) \<in># wP_of_wstate (lnth (ldrop (enat x) Sts) xb)"
    using assms(2)
    by (metis (no_types, lifting) comp_apply enat.distinct(2) enat_ord_code(4) lfinite_ldrop llength_eq_infty_conv_lfinite lnth_lmap)
  moreover
  from assms have "\<forall>n'<j. (C, n') \<notin> Sup_llist (lmap (set_mset \<circ> wP_of_wstate) (ldrop (enat x) Sts))" 
    unfolding is_least_def by auto
  then have "\<forall>n'. (C, n') \<in> Sup_llist (lmap (set_mset \<circ> wP_of_wstate) (ldrop (enat x) Sts)) \<longrightarrow> \<not>n'<j" 
    by auto
  then have "\<forall>n'. (C, n') \<in> Sup_llist (lmap (set_mset \<circ> wP_of_wstate) (ldrop (enat x) Sts)) \<longrightarrow> n' \<ge> j" 
    by auto
  then have "\<forall>n'. (C, n') \<in> Sup_llist (lmap (set_mset \<circ> wP_of_wstate) (ldrop (enat x) Sts)) \<longrightarrow> j \<le> n'" 
    by auto
  then have "\<forall>n' xa. (C, n') \<in># wP_of_wstate (lnth (ldrop (enat x) Sts) xa) \<longrightarrow> j \<le> n'"
    by (smt assms(2) enat.distinct(2) enat_ord_code(4) lfinite_ldrop llength_eq_infty_conv_lfinite 
         llength_lmap llist.map_comp lnth_lmap lnth_subset_Sup_llist subsetCE)
  ultimately show ?thesis
    by auto
qed

(* FIXME: come up with better name *)
lemma persistent_wclause_if_persistent_clause_P:
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
  (* FIXME: change name of ggg *)
  have ggg: "\<And>xa. C \<in> P_of_state (state_of_wstate (lnth (ldrop x Sts) xa))"
  proof - (* FIXME: should this be a lemma? *)
    fix xa :: "nat"
    have "enat xa < llength (ldrop (enat x) Sts)"
      using llength_infty
      by (simp add: ldrop_enat) 
    then have llen: "enat x + enat xa < llength  Sts"
      using llength_infty by auto
    then have "enat (x + xa) < llength  Sts"
      by auto
    then have "C \<in> P_of_state (state_of_wstate (lnth Sts (xa + x)))"
      using x_p(2)[of "x + xa"] by (simp add: add.commute) 
    then show "C \<in> P_of_state (state_of_wstate (lnth (ldrop (enat x) Sts) xa))"
      using lnth_ldrop[of "enat x" xa Sts] using llen by auto
  qed
  (* FIXME: give this a better name *)
  have stuff: "\<forall>xa. \<exists>i. (C,i) \<in># wP_of_wstate (lnth (ldrop x Sts) xa)"
    apply auto
    subgoal for xa
      using ggg[of xa]
      apply (cases "(lnth (ldrop (enat x) Sts)) xa")
      apply auto
      done
    done
  (* FIXME: come up with a better name or inline *)
  define magic where "magic = (\<lambda>i. (C, i) \<in> Sup_llist (lmap (set_mset \<circ> wP_of_wstate) (ldrop x Sts)))"
  have "magic i"
    unfolding magic_def using i_p assms(1) Supremum_drop_and_more by auto
  then obtain j where "is_least magic j"
    unfolding magic_def[symmetric] using least_exists by metis
  then have "\<exists>xb. (\<forall>k xa. (C, k) \<in># wP_of_wstate (lnth (ldrop x Sts) xa) \<longrightarrow> j \<le> k)
     \<and> (C,j) \<in># wP_of_wstate (lnth (ldrop x Sts) xb)"
    using assms(1) unfolding magic_def using is_least_reformulation by auto
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
      have ttt: "enat (Suc (x + xb + xc)) < llength Sts"
        by (simp add: llength_infty)
      have ttttt: "\<forall>ja. (C, ja) \<in># wP_of_wstate (lnth Sts (x + xb + xc)) \<longrightarrow> j \<le> ja"
      proof (rule, rule)
        fix ja :: "nat"
        assume "(C, ja) \<in># wP_of_wstate (lnth Sts (x + xb + xc))"
        then have "(C, ja) \<in># wP_of_wstate (lnth (ldrop (enat x) Sts) (xb + xc))"
          by (simp add: add.commute add.left_commute llength_infty)
        then show "j \<le> ja" 
          using j_p(1) by auto
      qed
      from Suc have "(C, j) \<in># wP_of_wstate (lnth (ldrop (x+xb) Sts) xc)"
        by blast
      then have tt: "(C, j) \<in># wP_of_wstate (lnth Sts ((x+xb) + xc))"
        by (simp add: add.commute llength_infty)
      moreover have "C \<in> P_of_state (state_of_wstate (lnth Sts (Suc (x + xb + xc))))"
        using ttt x_p(2) by auto
      then have "\<exists>k. (C, k) \<in># wP_of_wstate (lnth Sts (Suc (x + xb + xc)))"
        by (smt stuff add.commute add.left_commute add_Suc_right enat_ord_code(4) ldrop_enat llength_infty lnth_ldropn)
      ultimately have "(C, j) \<in># wP_of_wstate (lnth Sts (Suc (x + xb + xc)))"
        using stay_or_delete_completely_STRONGER[of "x + xb + xc" C j, OF ttt tt ttttt] by auto
      then have "(C, j) \<in># lnth (lmap wP_of_wstate Sts) (Suc ((x+xb) + xc))"
        by (simp add: llength_infty)
      then show ?case
        by (smt add.commute add_Suc_right lnth_ldrop lnth_lmap plus_enat_simps(1) the_enat.simps ttt)
    qed
    done
  have "(\<And>xa. x+xb \<le> xa \<Longrightarrow> (C, j) \<in># wP_of_wstate (lnth Sts xa))"
  proof -
    fix xa :: "nat"
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
      unfolding P_def by  (cases "llast Sts") auto
    then obtain D j where min: "(\<forall>(D', j') \<in># P - {#(D, j)#}. weight (D, j) \<le> weight (D', j'))"
      and Dj_in_p:"(D, j) \<in># P"
      sorry (* easily believable *)
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
   then show "False"
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

find_theorems ldrop Suc ltl

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



theorem weighted_RP_fair: "fair_state_seq (lmap state_of_wstate Sts)"
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
    then obtain i where "(C, i) \<in> Liminf_llist (lmap (set_mset \<circ> wN_of_wstate) Sts)" 
      using persistent_wclause_if_persistent_clause_P[of C] inf sorry 
      (* You need a persistent_wclause_if_persistent_clause for N.
         No. You don't need that. The following arguments should work even when the
         numbers change! *)
    then obtain k where k_p: "enat k < llength Sts"
      "\<And>j. k \<le> j \<Longrightarrow> enat j < llength Sts \<Longrightarrow> (C, i) \<in># wN_of_wstate (lnth Sts j)"
      unfolding Liminf_llist_def by auto
    have "chain op \<leadsto>\<^sub>w (ldrop k Sts)"
      using deriv inf inff inf_chain_ldrop_chain by auto
    moreover have "\<And>j. (C, i) \<in># wN_of_wstate (lnth (ldrop k Sts) j)"
      using k_p(2) by (simp add: add.commute inf)
    ultimately have "chain op \<leadsto>\<^sub>w\<^sub>n\<^sub>i (ldrop k Sts)"
      using inf inff sorry
    then have "chain (\<lambda>x y. (x, y) \<in> RP_Non_Inference_relation)\<inverse>\<inverse> (lmap RP_Non_Inference_measure (ldrop k Sts))"
      using inff inf
    proof (coinduction arbitrary: k rule: chain.coinduct)
      case chain
      then have k_lt_len: "enat k < llength Sts"
        by auto
      define x where "x = RP_Non_Inference_measure (lnth Sts k)"
      define xs where "xs = lmap RP_Non_Inference_measure (ldrop (enat (Suc k)) Sts)"
      have "(ldrop (enat k) Sts) = LCons ((lhd (ldrop (enat k) Sts))) ((ltl (ldrop (enat k) Sts)))"
         using chain(2)
        unfolding ldrop_Suc_conv_ltl
        unfolding lhd_ldrop'[symmetric, OF k_lt_len]
        by (metis enat.distinct(1) lfinite_LNil lfinite_ldrop llist.exhaust_sel)
      then have "lmap RP_Non_Inference_measure (ldrop (enat k) Sts) = LCons x xs"        
        unfolding x_def xs_def using chain
        by (metis (no_types, lifting) k_lt_len ldrop_Suc_conv_ltl lhd_ldrop' llist.simps(13)) 
      find_theorems ldrop Suc ltl
      moreover
      have "chain op \<leadsto>\<^sub>w\<^sub>n\<^sub>i (ldrop (enat (Suc k)) Sts)"
        using chain
        unfolding ldrop_Suc_conv_ltl
        using inf_chain_ltl_chain[of "op \<leadsto>\<^sub>w\<^sub>n\<^sub>i" "(ldrop (enat k) Sts)"]
        by (simp add: not_lfinite_llength)
      moreover
      have "lnth (ldrop (enat k) Sts) 0 \<leadsto>\<^sub>w\<^sub>n\<^sub>i lnth (ldrop (enat k) Sts) (Suc 0)"
        using chain chain_lnth_rel[of "op \<leadsto>\<^sub>w\<^sub>n\<^sub>i" "(ldrop (enat k) Sts)" 0]
        by (metis enat.distinct(2) enat_ord_code(4) lfinite_ldrop llength_eq_infty_conv_lfinite)
      then have "lnth Sts k \<leadsto>\<^sub>w\<^sub>n\<^sub>i lnth Sts (Suc k)"
        using lnth_ldrop[of k 0 Sts] lnth_ldrop[of k "Suc 0" Sts]
        by (simp add: inf)
      then have "(RP_Non_Inference_measure (lnth Sts (Suc k)), RP_Non_Inference_measure (lnth Sts k)) \<in> RP_Non_Inference_relation"
        using chain weighted_RP_Non_Inference_has_measure[of "lnth Sts k" "lnth Sts (Suc k)"] by auto
      then have "(lhd xs, x) \<in> RP_Non_Inference_relation"
        unfolding xs_def x_def
        by (simp add: inf lhd_ldrop')
      then have "(\<lambda>x y. (x, y) \<in> RP_Non_Inference_relation)\<inverse>\<inverse> x (lhd xs)"
        by auto
      ultimately show ?case
        using chain xs_def by auto
    qed
    then show False
      using wfP_iff_no_infinite_down_chain[of "\<lambda>x y. (x, y) \<in> RP_Non_Inference_relation"] 
        wf_RP_Non_Inference_relation inff
      by (metis (no_types, lifting) inf_llist_lnth ldrop_enat_inf_llist lfinite_inf_llist 
        lfinite_lmap wfPUNIVI wf_induct_rule)
  next
    assume asm: "C \<in> Liminf_llist (lmap P_of_state (lmap state_of_wstate Sts))"
    from asm obtain i where i_p:
      "enat i < llength Sts"
      "\<And>j. i \<le> j \<and> enat j < llength Sts \<Longrightarrow> C \<in> P_of_state (state_of_wstate (lnth Sts j))"
      unfolding Liminf_llist_def by auto
    then obtain i where "(C, i) \<in> Liminf_llist (lmap (set_mset \<circ> wP_of_wstate) Sts)"
      using persistent_wclause_if_persistent_clause_P[of C] using asm inf by auto
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
