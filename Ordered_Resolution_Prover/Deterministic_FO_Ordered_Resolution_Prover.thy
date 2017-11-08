(*  Title:       A Deterministic Ordered Resolution Prover for First-Order Clauses
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>A Deterministic Ordered Resolution Prover for First-Order Clauses\<close>

text \<open>
TODO.
\<close>

theory Deterministic_FO_Ordered_Resolution_Prover
  imports Weighted_FO_Ordered_Resolution_Prover
begin

type_synonym 'a lclause = "'a literal list"
type_synonym 'a glclause = "'a lclause \<times> nat"
type_synonym 'a glstate = "'a glclause list \<times> 'a glclause list \<times> 'a glclause list \<times> nat"

locale deterministic_FO_resolution_prover =
  weighted_FO_resolution_prover_with_size_generation_factors S subst_atm id_subst comp_subst
    renamings_apart atm_of_atms mgu less_atm size_atm generation_factor size_factor
  for
    S :: "('a :: wellorder) clause \<Rightarrow> 'a clause" and
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a literal multiset list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and
    size_atm :: "'a \<Rightarrow> nat" and
    generation_factor :: nat and
    size_factor :: nat +
  assumes
    S_empty: "S C = {#}"
begin

fun gstate_of_glstate :: "'a glstate \<Rightarrow> 'a gstate" where
  "gstate_of_glstate (N, P, Q, n) =
   (mset (map (apfst mset) N), mset (map (apfst mset) P), mset (map (apfst mset) Q), n)"

fun state_of_glstate :: "'a glstate \<Rightarrow> 'a state" where
  "state_of_glstate (N, P, Q, _) =
   (set (map (mset \<circ> fst) N), set (map (mset \<circ> fst) P), set (map (mset \<circ> fst) Q))"

fun is_final_glstate :: "'a glstate \<Rightarrow> bool" where
  "is_final_glstate (N, P, Q, n) \<longleftrightarrow> N = [] \<and> P = []"

abbreviation rtrancl_weighted_RP (infix "\<leadsto>\<^sub>w\<^sup>*" 50) where
  "op \<leadsto>\<^sub>w\<^sup>* \<equiv> (op \<leadsto>\<^sub>w)\<^sup>*\<^sup>*"

abbreviation trancl_weighted_RP (infix "\<leadsto>\<^sub>w\<^sup>+" 50) where
  "op \<leadsto>\<^sub>w\<^sup>+ \<equiv> (op \<leadsto>\<^sub>w)\<^sup>+\<^sup>+"

(* FIXME: prove and move to right locale/file, and prove for nonweighted version first *)
lemma weighted_RP_sound:
  "St \<leadsto>\<^sub>w St' \<Longrightarrow> I \<Turnstile>s grounding_of_state (state_of_gstate St) \<Longrightarrow>
   I \<Turnstile>s grounding_of_state (state_of_gstate St')"
  sorry

lemma rtrancl_weighted_RP_sound:
  "St \<leadsto>\<^sub>w\<^sup>* St' \<Longrightarrow> I \<Turnstile>s grounding_of_state (state_of_gstate St) \<Longrightarrow>
   I \<Turnstile>s grounding_of_state (state_of_gstate St')"
  by (induct rule: rtranclp.induct, assumption, metis weighted_RP_sound)

definition is_tautology :: "'a lclause \<Rightarrow> bool" where
  "is_tautology C \<longleftrightarrow> (\<exists>A \<in> set (map atm_of C). Pos A \<in> set C \<and> Neg A \<in> set C)"

definition is_subsumed_by :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> bool" where
  "is_subsumed_by Ds C \<longleftrightarrow> (\<exists>D \<in> set Ds. subsumes (mset D) (mset C))"

definition is_strictly_subsumed_by :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> bool" where
  "is_strictly_subsumed_by Ds C \<longleftrightarrow> (\<exists>D \<in> set Ds. strictly_subsumes (mset D) (mset C))"

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

fun deterministic_RP_step :: "'a glstate \<Rightarrow> 'a glstate" where
  "deterministic_RP_step (N, P, Q, n) =
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
        if C = [] \<and> [] \<notin> set (map fst (P @ Q)) then
          ([], [], [([], i)], Suc n)
        else if is_tautology C \<or> is_subsumed_by (map fst (P @ Q)) C then
          (N, P, Q, n)
        else
          let
            (back_to_P, Q) = reduce_all [C] Q;
            P = back_to_P @ P;
            P = case_prod (op @) (reduce_all [C] P);
            Q = filter (is_strictly_subsumed_by [C] \<circ> fst) Q;
            P = filter (is_strictly_subsumed_by [C] \<circ> fst) P;
            P = (C, i) # P
          in
            (N, P, Q, n))"

declare deterministic_RP_step.simps [simp del]

partial_function (option) deterministic_RP :: "'a glstate \<Rightarrow> 'a lclause list option" where
  "deterministic_RP St =
   (if is_final_glstate St then
      let (_, _, Q, _) = St in Some (map fst Q)
    else
      deterministic_RP (deterministic_RP_step St))"

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

lemma nonfinal_deterministic_RP_step:
  assumes
    nonfinal: "\<not> is_final_glstate St" and
    step: "St' = deterministic_RP_step St"
  shows "gstate_of_glstate St \<leadsto>\<^sub>w\<^sup>+ gstate_of_glstate St'"
proof -
  obtain N P Q :: "'a glclause list" and n :: nat where
    st: "St = (N, P, Q, n)"
    by (cases St) blast
  note step = step[unfolded st deterministic_RP_step.simps, simplified]

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

      (* FIXME: rename and state at different level of abstraction *)
      have trans:
        "({#}, mset (map (apfst mset) P'') + {#(mset C, i)#}, mset (map (apfst mset) Q), n)
         \<leadsto>\<^sub>w (mset (map (apfst mset) N'), mset (map (apfst mset) P''),
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
        apply (rule arg_cong2[of _ _ _ _ "op \<leadsto>\<^sub>w", THEN iffD1, OF _ _ trans[unfolded P''_def N'_def]])
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

    have "gstate_of_glstate ((E @ C, i) # N', P, Q, n)
       \<leadsto>\<^sub>w\<^sup>* gstate_of_glstate ((E @ reduce (map fst P @ map fst Q) E C, i) # N', P, Q, n)" for E
      unfolding C'_def
    proof (induct C arbitrary: E)
      case (Cons L C)
      note ih = this(1)
      show ?case
      proof (cases "is_reducible_lit (map fst P @ map fst Q) (E @ C) L")
        case l_red: True
        then have red_lc:
          "reduce (map fst P @ map fst Q) E (L # C) = reduce (map fst P @ map fst Q) E C"
          by simp
        from l_red obtain D D' :: "'a literal list" and L' :: "'a literal" and \<sigma> :: 's where
          "D \<in> set (map fst P @ map fst Q)" and
          "D' = remove1 L' D" and
          "L' \<in> set D" and
          "- L = L' \<cdot>l \<sigma>" and
          "mset D' \<cdot> \<sigma> \<subseteq># mset (E @ C)"
          unfolding is_reducible_lit_def comp_def by blast
        then have \<sigma>:
          "mset D' + {#L'#} \<in> set (map (mset \<circ> fst) (P @ Q))"
          "- L = L' \<cdot>l \<sigma> \<and> mset D' \<cdot> \<sigma> \<subseteq># mset (E @ C)"
          unfolding is_reducible_lit_def by (auto simp: comp_def)
        have "gstate_of_glstate ((E @ L # C, i) # N', P, Q, n)
          \<leadsto>\<^sub>w gstate_of_glstate ((E @ C, i) # N', P, Q, n)"
          by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
                forward_reduction[of "mset (map (apfst mset) P)" "mset (map (apfst mset) Q)" L \<sigma>
                  "mset (E @ C)" "mset (map (apfst mset) N')" i n]])
            (use \<sigma> in \<open>auto simp: comp_def\<close>)
        then show ?thesis
          unfolding red_lc using ih[of E] by (rule converse_rtranclp_into_rtranclp)
      next
        case False
        then show ?thesis
          using ih[of "L # E"] by simp
      qed
    qed simp
    then have red_C:
      "gstate_of_glstate ((C, i) # N', P, Q, n) \<leadsto>\<^sub>w\<^sup>* gstate_of_glstate ((C', i) # N', P, Q, n)"
      unfolding C'_def by (metis self_append_conv2)

    have proc_C: "gstate_of_glstate ((C', i) # N', P', Q', n')
      \<leadsto>\<^sub>w gstate_of_glstate (N', (C', i) # P', Q', n')" for P' Q' n'
      by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
            clause_processing[of "mset (map (apfst mset) N')" "mset C'" i
              "mset (map (apfst mset) P')" "mset (map (apfst mset) Q')" n']],
          simp+)

    show ?thesis
    proof (cases "C' = [] \<and> [] \<notin> fst ` set P \<and> [] \<notin> fst ` set Q")
      case True
      note c'_nil = this[THEN conjunct1] and nil_ni_pq = this[THEN conjunct2]
      note step = step[simplified c'_nil nil_ni_pq, simplified]

      have sub_P:
        "gstate_of_glstate (([], i) # N', P, Q, n) \<leadsto>\<^sub>w\<^sup>* gstate_of_glstate (([], i) # N', [], Q, n)"
        using nil_ni_pq[THEN conjunct1]
      proof (induct P)
        case (Cons P0 P)
        note ih = this(1) and nil_ni_p = this(2)
        have "gstate_of_glstate (([], i) # N', P0 # P, Q, n)
          \<leadsto>\<^sub>w gstate_of_glstate (([], i) # N', P, Q, n)"
          by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
                backward_subsumption_P[of "mset (map (apfst mset) (([], i) # N'))" "mset (fst P0)"
                  "mset (map (apfst mset) P)" "snd P0" "mset (map (apfst mset) Q)" n]],
              cases P0, use nil_ni_p in auto)
        then show ?case
          using ih by (rule converse_rtranclp_into_rtranclp, use nil_ni_p in auto)
      qed simp
      have sub_Q:
        "gstate_of_glstate (([], i) # N', [], Q, n) \<leadsto>\<^sub>w\<^sup>* gstate_of_glstate (([], i) # N', [], [], n)"
        using nil_ni_pq[THEN conjunct2]
      proof (induct Q)
        case (Cons Q0 Q)
        note ih = this(1) and nil_ni_q = this(2)
        have "gstate_of_glstate (([], i) # N', [], Q0 # Q, n)
          \<leadsto>\<^sub>w gstate_of_glstate (([], i) # N', [], Q, n)"
          by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
                backward_subsumption_Q[of "mset (map (apfst mset) (([], i) # N'))" "mset (fst Q0)"
                  "{#}" "mset (map (apfst mset) Q)" "snd Q0" n]],
              cases Q0, use nil_ni_q in auto)
        then show ?case
          using ih by (rule converse_rtranclp_into_rtranclp, use nil_ni_q in auto)
      qed simp
      have sub_N:
        "gstate_of_glstate (N', [([], i)], [], n) \<leadsto>\<^sub>w\<^sup>* gstate_of_glstate ([], [([], i)], [], n)"
      proof (induct N')
        case (Cons N'0 N')
        note ih = this
        have "gstate_of_glstate (N'0 # N', [([], i)], [], n)
          \<leadsto>\<^sub>w gstate_of_glstate (N', [([], i)], [], n)"
          by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
                forward_subsumption[of "{#}" "{#({#}, i)#}" "{#}" "mset (fst N'0)"
                  "mset (map (apfst mset) N')" "snd N'0" n]])
            (cases N'0, auto)
        then show ?case
          using ih by (rule converse_rtranclp_into_rtranclp)
      qed simp
      have inf_C:
        "gstate_of_glstate ([], [([], i)], [], n) \<leadsto>\<^sub>w gstate_of_glstate ([], [], [([], i)], Suc n)"
        by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
              inference_computation[of "{#}" "{#}" i "{#}" n "{#}"]],
            auto simp: ord_FO_resolution_inferences_between_empty_empty)

      show ?thesis
        unfolding step st n_cons ci
        using red_C[unfolded c'_nil, THEN rtranclp_trans, OF sub_P,
          THEN rtranclp_trans, OF sub_Q,
          THEN rtranclp_into_tranclp1, OF proc_C[unfolded c'_nil],
          THEN tranclp_rtranclp_tranclp, OF sub_N,
          THEN tranclp.trancl_into_trancl, OF inf_C] .
    next
      case c'_nnil: False
      note step = step[simplified c'_nnil, simplified]
      show ?thesis
      proof (cases "is_tautology C' \<or> is_subsumed_by (map fst P @ map fst Q) C'")
        case taut_or_subs: True
        note step = step[simplified taut_or_subs, simplified]

        have "gstate_of_glstate ((C', i) # N', P, Q, n) \<leadsto>\<^sub>w gstate_of_glstate (N', P, Q, n)"
        proof (cases "is_tautology C'")
          case True
          then obtain A :: 'a where
            neg_a: "Neg A \<in> set C'" and pos_a: "Pos A \<in> set C'"
            unfolding is_tautology_def by blast
          show ?thesis
            by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
                  tautology_deletion[of A "mset C'" "mset (map (apfst mset) N')" i
                    "mset (map (apfst mset) P)" "mset (map (apfst mset) Q)" n]])
              (use neg_a pos_a in simp_all)
        next
          case False
          hence "is_subsumed_by (map fst P @ map fst Q) C'"
            using taut_or_subs by blast
          then obtain D where d:
            "D \<in> set (map fst P @ map fst Q)"
            "subsumes (mset D) (mset C')"
            unfolding is_subsumed_by_def by blast
          show ?thesis
            by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
                  forward_subsumption[of "mset D" "mset (map (apfst mset) P)"
                    "mset (map (apfst mset) Q)" "mset C'" "mset (map (apfst mset) N')" i n]])
              (use d in \<open>auto simp: is_subsumed_by_def\<close>)
        qed
        then show ?thesis
          unfolding step st n_cons ci using red_C by (rule rtranclp_into_tranclp1[rotated])
      next
        case not_taut_or_subs: False
        note step = step[simplified not_taut_or_subs, simplified]

        obtain back_to_P Q' :: "('a literal list \<times> nat) list" where
          red_Q: "(back_to_P, Q') = reduce_all [C'] Q"
          by (metis prod.exhaust)
        note step = step[unfolded red_Q[symmetric], simplified]

        define P' :: "('a literal list \<times> nat) list" where
          "P' = case_prod (op @) (reduce_all [C'] (back_to_P @ P))"
        define Q'' :: "('a literal list \<times> nat) list" where
          "Q'' = filter (is_strictly_subsumed_by [C'] \<circ> fst) Q'"
        define P'' :: "('a literal list \<times> nat) list" where
          "P'' = filter (is_strictly_subsumed_by [C'] \<circ> fst) P'"
        note step = step[unfolded P'_def[symmetric] Q''_def[symmetric] P''_def[symmetric],
            simplified]

        have red_Q: "gstate_of_glstate ((C', i) # N', P, Q, n)
          \<leadsto>\<^sub>w\<^sup>* gstate_of_glstate ((C', i) # N', back_to_P @ P, Q', n)"
          sorry
        have red_P: "gstate_of_glstate ((C', i) # N', back_to_P @ P, Q', n)
          \<leadsto>\<^sub>w\<^sup>* gstate_of_glstate ((C', i) # N', P', Q', n)"
          sorry
        have subs_Q: "gstate_of_glstate ((C', i) # N', P', Q', n)
          \<leadsto>\<^sub>w\<^sup>* gstate_of_glstate ((C', i) # N', P', Q'', n)"
          sorry
        have subs_P: "gstate_of_glstate ((C', i) # N', P', Q'', n)
          \<leadsto>\<^sub>w\<^sup>* gstate_of_glstate ((C', i) # N', P'', Q'', n)"
          sorry

        show ?thesis
          unfolding step st n_cons ci
          by (rule red_C[THEN rtranclp_trans, OF red_Q,
              THEN rtranclp_trans, OF red_P,
              THEN rtranclp_trans, OF subs_Q,
              THEN rtranclp_trans, OF subs_P,
              THEN rtranclp_into_tranclp1, OF proc_C])
      qed
    qed
  qed
qed

lemma final_deterministic_RP_step: "is_final_glstate St \<Longrightarrow> deterministic_RP_step St = St"
  by (cases St) (simp add: deterministic_RP_step.simps)

lemma deterministic_RP_SomeD:
  assumes "deterministic_RP (N, P, Q, n) = Some R"
  shows "\<exists>N' P' Q' n'.
    (\<exists>k. (deterministic_RP_step ^^ k) (N, P, Q, n) = (N', P', Q', n'))
     \<and> N' = [] \<and> P' = [] \<and> R = map fst Q'"
proof (induct rule: deterministic_RP.raw_induct[OF _ assms])
  case (1 self_call St R)
  note ih = this(1) and step = this(2)

  obtain N P Q :: "'a glclause list" and n :: nat where
    st: "St = (N, P, Q, n)"
    by (cases St) blast
  note step = step[unfolded st, simplified]

  show ?case
  proof (cases "N = [] \<and> P = []")
    case True
    then have "(deterministic_RP_step ^^ 0) (N, P, Q, n) = (N, P, Q, n)
      \<and> N = [] \<and> P = [] \<and> R = map fst Q"
      using step by simp
    then show ?thesis
      unfolding st by blast
  next
    case nonfinal: False
    note step = step[simplified nonfinal, simplified]

    obtain k N' P' Q' n' where
      "(deterministic_RP_step ^^ k)
        (deterministic_RP_step (N, P, Q, n)) = (N', P', Q', n')
       \<and> N' = [] \<and> P' = [] \<and> R = map fst Q'"
      using ih[OF step] by blast
    then show ?thesis
      unfolding st funpow_Suc_right[symmetric, THEN fun_cong, unfolded comp_apply] by blast
  qed
qed

lemma deterministic_RP_step_weighted:
  "gstate_of_glstate St \<leadsto>\<^sub>w\<^sup>* gstate_of_glstate (deterministic_RP_step St)"
  by (cases "is_final_glstate St")
    (simp add: final_deterministic_RP_step nonfinal_deterministic_RP_step tranclp_into_rtranclp)+

lemma deterministic_RP_step_funpow_weighted:
  "gstate_of_glstate St \<leadsto>\<^sub>w\<^sup>* gstate_of_glstate ((deterministic_RP_step ^^ k) St)"
  by (induct k; simp) (meson deterministic_RP_step_weighted rtranclp_trans)

lemma deterministic_RP_step_funpow_iff: "(\<exists>k. (deterministic_RP_step ^^ k) St = St') \<longleftrightarrow>
  gstate_of_glstate St \<leadsto>\<^sub>w\<^sup>* gstate_of_glstate St'" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    using deterministic_RP_step_funpow_weighted by blast
next
  show "?rhs \<Longrightarrow> ?lhs"
    apply (rule rtranclp.induct[of "\<lambda>St St'. gstate_of_glstate St \<leadsto>\<^sub>w gstate_of_glstate St'"])
      defer
    sorry
qed

theorem deterministic_RP_sound:
  assumes some: "deterministic_RP (N, [], [], n) = Some Q"
  shows
    "src.saturated_upto (set (map mset Q)) \<and>
     (satisfiable (set (map mset Q)) \<longleftrightarrow> satisfiable (set (map (mset \<circ> fst) N)))"
  using deterministic_RP_SomeD[OF some, unfolded step_funpow_iff]
  using saturated
  sorry

theorem deterministic_RP_complete:
  assumes "\<exists>Q. finite Q \<and> src.saturated_upto Q \<and> (satisfiable Q \<longleftrightarrow> satisfiable (set (map mset N)))"
  shows "deterministic_RP (map (\<lambda>D. (D, 0)) N, [], [], 1) \<noteq> None"
  sorry

end

end
