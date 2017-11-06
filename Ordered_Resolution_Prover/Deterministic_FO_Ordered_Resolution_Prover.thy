(*  Title:       A Deterministic Ordered Resolution Prover for First-Order Clauses
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>A Deterministic Ordered Resolution Prover for First-Order Clauses\<close>

text \<open>
TODO.
\<close>

theory Deterministic_FO_Ordered_Resolution_Prover
  imports Fair_FO_Ordered_Resolution_Prover
begin

type_synonym 'a lclause = "'a literal list"
type_synonym 'a glclause = "'a lclause \<times> nat"
type_synonym 'a glstate = "'a glclause list \<times> 'a glclause list \<times> 'a glclause list \<times> nat"

locale deterministic_FO_resolution_prover = fair_FO_resolution_prover_with_sum_product
begin

fun gstate_of_glstate :: "'a glstate \<Rightarrow> 'a gstate" where
  "gstate_of_glstate (N, P, Q, n) =
   (mset (map (apfst mset) N), mset (map (apfst mset) P), mset (map (apfst mset) Q), n)"

fun state_of_glstate :: "'a glstate \<Rightarrow> 'a state" where
  "state_of_glstate (N, P, Q, _) =
   (set (map (mset \<circ> fst) N), set (map (mset \<circ> fst) P), set (map (mset \<circ> fst) Q))"

fun is_final_glstate :: "'a glstate \<Rightarrow> bool" where
  "is_final_glstate (N, P, Q, n) \<longleftrightarrow> N = [] \<and> P = []"

abbreviation rtrancl_resolution_prover_with_weights (infix "\<leadsto>\<^sub>f\<^sup>*" 50) where
  "op \<leadsto>\<^sub>f\<^sup>* \<equiv> (op \<leadsto>\<^sub>f)\<^sup>*\<^sup>*"

abbreviation trancl_resolution_prover_with_weights (infix "\<leadsto>\<^sub>f\<^sup>+" 50) where
  "op \<leadsto>\<^sub>f\<^sup>+ \<equiv> (op \<leadsto>\<^sub>f)\<^sup>+\<^sup>+"

(* FIXME: prove and move to right locale/file, and prove for non-fair version first *)
lemma resolution_prover_with_weights_sound:
  "St \<leadsto>\<^sub>f St' \<Longrightarrow> I \<Turnstile>s grounding_of_state (state_of_gstate St) \<Longrightarrow>
   I \<Turnstile>s grounding_of_state (state_of_gstate St')"
  sorry

lemma rtrancl_resolution_prover_with_weights_sound:
  "St \<leadsto>\<^sub>f\<^sup>* St' \<Longrightarrow> I \<Turnstile>s grounding_of_state (state_of_gstate St) \<Longrightarrow>
   I \<Turnstile>s grounding_of_state (state_of_gstate St')"
  by (induct rule: rtranclp.induct, assumption, metis resolution_prover_with_weights_sound)

definition is_tautology :: "'a lclause \<Rightarrow> bool" where
  "is_tautology C \<longleftrightarrow> (\<exists>A \<in> set (map atm_of C). Pos A \<in> set C \<and> Neg A \<in> set C)"

definition is_subsumed_by :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> bool" where
  "is_subsumed_by Ds C \<longleftrightarrow> (\<exists>D \<in> set Ds. subsumes (mset D) (mset C))"

definition is_reducible_lit :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> 'a literal \<Rightarrow> bool" where
  "is_reducible_lit Ds C L \<longleftrightarrow>
   (\<exists>D \<in> set Ds. \<exists>L' \<in> set D. \<exists>\<sigma>. - L = L' \<cdot>l \<sigma> \<and> mset (remove1 L' D) \<cdot> \<sigma> \<subseteq># mset C)"

primrec reduce :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause" where
  "reduce _ _ [] = []"
| "reduce Ds C (L # C') =
   (if is_reducible_lit Ds (C @ C') L then reduce Ds C C' else L # reduce Ds (L # C) C')"

fun reduce_all :: "'a lclause list \<Rightarrow> 'a glclause list \<Rightarrow> 'a glclause list \<times> 'a glclause list" where
  "reduce_all _ [] = ([], [])"
| "reduce_all Ds ((C, i) # Cs) =
   (let C' = reduce Ds [] C in
      (if length C' = length C then apsnd else apfst) (Cons (C', i)) (reduce_all Ds Cs))"

fun resolve_on :: "'a lclause \<Rightarrow> 'a \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause list" where
  "resolve_on C B D =
   concat (map (\<lambda>L.
     (case L of
        Neg _ \<Rightarrow> []
      | Pos A \<Rightarrow>
        (case mgu {{A, B}} of
           None \<Rightarrow> []
         | Some \<sigma> \<Rightarrow>
           let
             D' = map (\<lambda>M. M \<cdot>l \<sigma>) D;
             B' = B \<cdot>a \<sigma>
           in
             if maximal_in B' (mset D') then
               let
                 C' = map (\<lambda>L. L \<cdot>l \<sigma>) (removeAll L C)
               in
                 (if strictly_maximal_in B' (mset C') then [C' @ D'] else []) @ resolve_on C' B' D'
             else
               []))) C)"

definition resolve :: "'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause list" where
  "resolve C D =
   concat (map (\<lambda>M.
     (case M of
        Pos A \<Rightarrow> []
      | Neg A \<Rightarrow>
        if maximal_in A (mset D) then
          resolve_on C A (remove1 M D)
        else
          [])) D)"

definition resolve_either_way :: "'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause list" where
  "resolve_either_way C D = resolve C D @ resolve D C"

definition resolve_rename :: "'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause list" where
  "resolve_rename C D =
   (let \<sigma>s = renamings_apart [mset C, mset D] in
    resolve (map (\<lambda>L. L \<cdot>l (\<sigma>s ! 0)) C) (map (\<lambda>L. L \<cdot>l (\<sigma>s ! 1)) D))"

definition resolve_rename_either_way :: "'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause list" where
  "resolve_rename_either_way C D =
   (let \<sigma>s = renamings_apart [mset C, mset D] in
    resolve_either_way (map (\<lambda>L. L \<cdot>l (\<sigma>s ! 0)) C) (map (\<lambda>L. L \<cdot>l (\<sigma>s ! 1)) D))"

fun
  select_min_weight_clause :: "'a glclause \<Rightarrow> 'a glclause list \<Rightarrow> 'a glclause"
where
  "select_min_weight_clause Ci [] = Ci"
| "select_min_weight_clause Ci (Dj # Ds) =
   select_min_weight_clause (if weight (apfst mset Dj) < weight (apfst mset Ci) then Dj else Ci) Ds"

fun deterministic_resolution_prover_step :: "'a glstate \<Rightarrow> 'a glstate" where
  "deterministic_resolution_prover_step (N, P, Q, n) =
   (case N of
      [] \<Rightarrow>
      (case P of
         [] \<Rightarrow> (N, P, Q, n)
       | P0 # P' \<Rightarrow>
         let
           (C, i) = select_min_weight_clause P0 P';
           N = map (\<lambda>D. (D, n))
             (remdups (resolve_rename C C @ concat (map (resolve_rename_either_way C \<circ> fst) Q)));
           P = remove1 (C, i) P;
           Q = (C, i) # Q;
           n = Suc n
         in
           (N, P, Q, n))
    | (C, i) # N \<Rightarrow>
      let
        C = reduce (map fst (P @ Q)) [] C
      in
        if C = [] then
          ([], [], [([], i)], Suc n)
        else if is_tautology C \<or> is_subsumed_by (map fst (P @ Q)) C then
          (N, P, Q, n)
        else
          let
            (back_to_P, Q) = reduce_all [C] Q;
            P = back_to_P @ P;
            P = case_prod (op @) (reduce_all [C] P);
            Q = filter (is_subsumed_by [C] \<circ> fst) Q;
            P = filter (is_subsumed_by [C] \<circ> fst) P;
            P = (C, i) # P
          in
            (N, P, Q, n))"

partial_function (option)
  deterministic_resolution_prover :: "'a glstate \<Rightarrow> 'a lclause list option"
where
  "deterministic_resolution_prover St =
   (if is_final_glstate St then
      let (_, _, Q, _) = St in Some (map fst Q)
    else
      deterministic_resolution_prover (deterministic_resolution_prover_step St))"

lemma select_min_weight_clause_in: "select_min_weight_clause P0 P \<in> set (P0 # P)"
  by (induct P arbitrary: P0) auto

lemma select_min_weight_clause_min_weight:
  assumes "Ci = select_min_weight_clause P0 P"
  shows "weight (apfst mset Ci) = Min ((weight \<circ> apfst mset) ` set (P0 # P))"
  using assms
proof (induct P arbitrary: P0 Ci)
  case (Cons P1 P)
  note ih = this(1) and ci = this(2)
  show ?case
  proof (cases "weight (apfst mset P1) < weight (apfst mset P0)")
    case True
    then have min: "Min ((weight \<circ> apfst mset) ` set (P0 # P1 # P)) =
      Min ((weight \<circ> apfst mset) ` set (P1 # P))"
      by (simp add: min_def)
    show ?thesis
      unfolding min by (rule ih[of Ci P1]) (simp add: ih[of Ci P1] ci True)
  next
    case False
    have "Min ((weight \<circ> apfst mset) ` set (P0 # P1 # P)) =
      Min ((weight \<circ> apfst mset) ` set (P1 # P0 # P))"
      by (rule arg_cong[of _ _ Min]) auto
    then have min: "Min ((weight \<circ> apfst mset) ` set (P0 # P1 # P)) =
      Min ((weight \<circ> apfst mset) ` set (P0 # P))"
      by (simp add: min_def) (smt False List.finite_set Min_insert2 Suc_le_eq antisym finite_imageI
          imageE not_less_eq_eq o_def)
    show ?thesis
      unfolding min by (rule ih[of Ci P0]) (simp add: ih[of Ci P1] ci False)
  qed
qed simp

(* FIXME: inline below?
lemma reduce_N_simulation:
  "(N + {(mset (C @ C'), i)}, set (map (apfst mset) P), set (map (apfst mset) Q), n)
    \<leadsto>\<^sub>f\<^sup>* (N \<union> {(mset (C @ reduce (map fst (P @ Q)) C C'), i)}, set (map (apfst mset) P),
         set (map (apfst mset) Q), n)"
proof (induct C' arbitrary: C)
  case (Cons L C')
  note ih = this
  show ?case
  proof (cases "is_reducible_lit (map fst P @ map fst Q) (C @ C') L")
    case red: True
    then have red_c: "reduce (map fst (P @ Q)) C (L # C') = reduce (map fst (P @ Q)) C C'"
      by simp

    have foo: "\<exists>D L' j \<sigma>. (D + {#L'#}, j) \<in> set (map (apfst mset) P) \<union> set (map (apfst mset) Q) \<and>
       - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># mset (C @ C')"
      sorry

    show ?thesis
      apply (rule converse_rtranclp_into_rtranclp)
       defer
      apply (simp only: red_c)
       apply (rule ih[of C])
(*
      using forward_reduction[of "set (map (apfst mset) P)" "set (map (apfst mset) Q)" L _ "mset (C @ C')" N i n]
*)
      apply simp
      sorry
  next
    case False
    then show ?thesis
      using ih[of "L # C"] by simp
  qed
qed simp
*)

lemma deterministic_resolution_prover_step_simulation_nonfinal:
  assumes
    nonfinal: "\<not> is_final_glstate St" and
    step: "St' = deterministic_resolution_prover_step St"
  shows "gstate_of_glstate St \<leadsto>\<^sub>f\<^sup>+ gstate_of_glstate St'"
proof -
  obtain N P Q :: "'a glclause list" and n :: nat where
    st: "St = (N, P, Q, n)"
    by (cases St) blast
  note step = step[unfolded st, simplified]

  show ?thesis
  proof (cases N)
    case n_nil: Nil
    note step = step[unfolded n_nil, simplified]
    show ?thesis
    proof (cases P)
      case Nil
      then have False
        using n_nil nonfinal[unfolded st] by simp
      then show ?thesis
        using step by simp
    next
      case p_cons: (Cons P0 P')
      note step = step[unfolded p_cons, simplified]

      obtain C :: "'a lclause" and i :: nat where
        ci: "(C, i) = select_min_weight_clause P0 P'"
        by (cases "select_min_weight_clause P0 P'") simp
      note step = step[unfolded select, simplified, folded remove1.simps(2)]

      have ci_in: "(C, i) \<in> set P"
        by (rule select_min_weight_clause_in[of P0 P', folded ci p_cons])

      define N' :: "'a glclause list" where
        "N' = map (\<lambda>D. (D, n))
           (remdups (resolve_rename C C @ concat (map (resolve_rename_either_way C \<circ> fst) Q)))"
      define P'' :: "'a glclause list" where
        "P'' = remove1 (C, i) P"

      have trans:
        "({#}, mset (map (apfst mset) P'') + {#(mset C, i)#}, mset (map (apfst mset) Q), n)
         \<leadsto>\<^sub>f (mset (map (apfst mset) N'), mset (map (apfst mset) P''),
              mset (map (apfst mset) Q) + {#(mset C, i)#}, Suc n)"
      proof (rule inference_computation)
        have "\<forall>(D, j) \<in># mset (map (apfst mset) P). weight (mset C, i) \<le> weight (D, j)"
          unfolding select_min_weight_clause_min_weight[OF ci, simplified] p_cons by simp
        moreover have "mset (map (apfst mset) P'') \<subseteq># mset (map (apfst mset) P)"
          unfolding P''_def by (simp add: image_mset_subseteq_mono)
        ultimately show "\<forall>(D, j) \<in># mset (map (apfst mset) P''). weight (mset C, i) \<le> weight (D, j)"
          by fast
      next
        show "mset (map (apfst mset) N') = mset_set ((\<lambda>D. (D, n)) `
          concls_of (ord_FO_resolution_inferences_between (set_mset (image_mset fst
            (mset (map (apfst mset) Q)))) (mset C)))"
          unfolding N'_def ord_FO_resolution_inferences_between_def
            inference_system.inferences_between_def ord_FO_\<Gamma>_def infer_from_def
        proof (induct Q)
          case Nil
          then show ?case
            apply simp
            sorry
        next
          case (Cons a Q)
          then show ?case sorry
        qed
      qed

      show ?thesis
        unfolding st n_nil step
        apply (rule tranclp.r_into_trancl)
        apply (unfold gstate_of_glstate.simps)
        apply (fold ci)
        apply (simp del: remove1.simps)
        apply (rule arg_cong2[of _ _ _ _ "op \<leadsto>\<^sub>f", THEN iffD1, OF _ _ trans[unfolded P''_def N'_def]])
         apply simp
        using ci_in
         apply (metis (no_types) apfst_conv image_mset_add_mset insert_DiffM set_mset_mset)
        apply (simp add: p_cons)
        done
    qed
  next
    case n_cons: (Cons Ci N')
    note step = step[unfolded n_cons, simplified]

    obtain C :: "'a lclause" and i :: nat where
      ci: "Ci = (C, i)"
      by (cases Ci) simp
    note step = step[unfolded ci, simplified]

    define C' :: "'a lclause" where
      "C' = reduce (map fst P @ map fst Q) [] C"
    note step = step[unfolded ci C'_def[symmetric], simplified]

    show ?thesis
    proof (cases "C' = Nil")
      case c'_nil: True
      note step = step[unfolded c'_nil, simplified]

      have red_C_trans:
        "gstate_of_glstate ((C, i) # N', P, Q, n) \<leadsto>\<^sub>f\<^sup>* gstate_of_glstate (([], i) # N', P, Q, n)"
        sorry
      have sub_P_trans:
        "gstate_of_glstate (([], i) # N', P, Q, n) \<leadsto>\<^sub>f\<^sup>* gstate_of_glstate (([], i) # N', [], Q, n)"
      proof (induct P)
        case (Cons P0 P)
        note ih = this
        have "gstate_of_glstate (([], i) # N', P0 # P, Q, n)
          \<leadsto>\<^sub>f gstate_of_glstate (([], i) # N', P, Q, n)"
          apply (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>f", OF _ _
                backward_subsumption_P[of "mset (map (apfst mset) (([], i) # N'))" "mset (fst P0)"
                  "mset (map (apfst mset) P)" "snd P0" "mset (map (apfst mset) Q)" n]])
            apply (cases "P0")
            apply simp
           apply simp
          apply simp
          sorry
        then show ?case
          using ih by (rule converse_rtranclp_into_rtranclp)
      qed simp
      have sub_Q_trans:
        "gstate_of_glstate (([], i) # N', [], Q, n) \<leadsto>\<^sub>f\<^sup>* gstate_of_glstate (([], i) # N', [], [], n)"
        sorry
      have proc_C_trans:
        "gstate_of_glstate (([], i) # N', [], [], n) \<leadsto>\<^sub>f gstate_of_glstate (N', [([], i)], [], n)"
        sorry
      have sub_N_trans:
        "gstate_of_glstate (N', [([], i)], [], n) \<leadsto>\<^sub>f\<^sup>* gstate_of_glstate ([], [([], i)], [], n)"
        sorry
      have inf_C_trans:
        "gstate_of_glstate ([], [([], i)], [], n) \<leadsto>\<^sub>f gstate_of_glstate ([], [], [([], i)], Suc n)"
        sorry

      show ?thesis
        unfolding step st n_cons ci
        using red_C_trans[THEN rtranclp_trans, OF sub_P_trans,
          THEN rtranclp_trans, OF sub_Q_trans,
          THEN rtranclp_into_tranclp1, OF proc_C_trans,
          THEN tranclp_rtranclp_tranclp, OF sub_N_trans,
          THEN tranclp.trancl_into_trancl, OF inf_C_trans] .
    next
      case c'_nnil: False
      note step = step[simplified c'_nnil, simplified]
      show ?thesis
      proof (cases "is_tautology C' \<or> is_subsumed_by (map fst P @ map fst Q) C'")
        case taut_or_subs: True
        note step = step[simplified taut_or_subs, simplified]
        show ?thesis
          unfolding st n_cons ci
          sorry
(* FIXME
          by (auto simp: clss_of_state_def grounding_of_clss_def)
*)
      next
        case not_taut_or_subs: False
        note step = step[simplified not_taut_or_subs, simplified]
        show ?thesis
          unfolding st n_cons ci
          (* use soundness of subsumption at calculus level *)
          sorry
      qed
    qed
  qed
qed

lemma deterministic_resolution_prover_step_simulation_final:
  assumes "is_final_glstate St"
  shows "\<not> gstate_of_glstate St \<leadsto>\<^sub>f St'"
  sorry

theorem deterministic_resolution_prover_sound:
  assumes "deterministic_resolution_prover (N, [], [], 1) = Some Q"
  shows
    "saturated_upto (set (map mset Q))"
    "satisfiable (set (map mset Q)) \<longleftrightarrow> satisfiable (set (map (mset \<circ> fst) N))"
  sorry

theorem deterministic_resolution_prover_complete:
  assumes "\<exists>Q. saturated_upto Q \<and> satisfiable Q \<longleftrightarrow> satisfiable (set (map mset N))"
  shows "deterministic_resolution_prover (map (\<lambda>D. (D, 0)) N, [], [], 1) \<noteq> None"
  sorry

end

end
