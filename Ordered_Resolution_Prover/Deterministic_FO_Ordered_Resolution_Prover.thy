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


section \<open>Library\<close>

(* TODO: Move to Isabelle. *)
lemma funpow_fixpoint: "f x = x \<Longrightarrow> (f ^^ n) x = x"
  by (induct n) auto

lemma rtranclp_imp_eq_image: "(\<forall>x y. R x y \<longrightarrow> f x = f y) \<Longrightarrow> R\<^sup>*\<^sup>* x y \<Longrightarrow> f x = f y"
  by (erule rtranclp.induct) auto

lemma tranclp_imp_eq_image: "(\<forall>x y. R x y \<longrightarrow> f x = f y) \<Longrightarrow> R\<^sup>+\<^sup>+ x y \<Longrightarrow> f x = f y"
  by (erule tranclp.induct) auto


section \<open>Prover\<close>

type_synonym 'a lclause = "'a literal list"
type_synonym 'a dclause = "'a lclause \<times> nat"
type_synonym 'a dstate = "'a dclause list \<times> 'a dclause list \<times> 'a dclause list \<times> nat"

locale deterministic_FO_resolution_prover =
  weighted_FO_resolution_prover_with_size_generation_factors S subst_atm id_subst comp_subst
    renamings_apart atm_of_atms mgu lessatm size_atm generation_factor size_factor
  for
    S :: "('a :: wellorder) clause \<Rightarrow> 'a clause" and
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a literal multiset list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    lessatm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and
    size_atm :: "'a \<Rightarrow> nat" and
    generation_factor :: nat and
    size_factor :: nat +
  assumes
    S_empty: "S C = {#}"
begin

fun wstate_of_dstate :: "'a dstate \<Rightarrow> 'a wstate" where
  "wstate_of_dstate (N, P, Q, n) =
   (mset (map (apfst mset) N), mset (map (apfst mset) P), mset (map (apfst mset) Q), n)"

fun state_of_dstate :: "'a dstate \<Rightarrow> 'a state" where
  "state_of_dstate (N, P, Q, _) =
   (set (map (mset \<circ> fst) N), set (map (mset \<circ> fst) P), set (map (mset \<circ> fst) Q))"

abbreviation clss_of_dstate :: "'a dstate \<Rightarrow> 'a clause set" where
  "clss_of_dstate St \<equiv> clss_of_state (state_of_dstate St)"

fun is_final_dstate :: "'a dstate \<Rightarrow> bool" where
  "is_final_dstate (N, P, Q, n) \<longleftrightarrow> N = [] \<and> P = [] \<or> [] \<in> fst ` set Q"

declare is_final_dstate.simps [simp del]

abbreviation rtrancl_weighted_RP (infix "\<leadsto>\<^sub>w\<^sup>*" 50) where
  "op \<leadsto>\<^sub>w\<^sup>* \<equiv> (op \<leadsto>\<^sub>w)\<^sup>*\<^sup>*"

abbreviation trancl_weighted_RP (infix "\<leadsto>\<^sub>w\<^sup>+" 50) where
  "op \<leadsto>\<^sub>w\<^sup>+ \<equiv> (op \<leadsto>\<^sub>w)\<^sup>+\<^sup>+"

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

fun reduce_all :: "'a lclause list \<Rightarrow> 'a dclause list \<Rightarrow> 'a dclause list \<times> 'a dclause list" where
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
  select_min_weight_clause :: "'a dclause \<Rightarrow> 'a dclause list \<Rightarrow> 'a dclause"
where
  "select_min_weight_clause Ci [] = Ci"
| "select_min_weight_clause Ci (Dj # Ds) =
   select_min_weight_clause (if weight (apfst mset Dj) < weight (apfst mset Ci) then Dj else Ci) Ds"

fun deterministic_RP_step :: "'a dstate \<Rightarrow> 'a dstate" where
  "deterministic_RP_step (N, P, Q, n) =
   (case List.find (\<lambda>(C, _). C = []) Q of
      Some _ \<Rightarrow> (N, P, Q, n)
    | None \<Rightarrow>
      (case List.find (\<lambda>(C, _). C = []) P of
         Some Ci \<Rightarrow> (N, P, Ci # Q, Suc n)
       | None \<Rightarrow>
         (case N of
           [] \<Rightarrow>
           (case P of
              [] \<Rightarrow> (N, P, Q, n)
            | P0 # P' \<Rightarrow>
              let
                (C, i) = select_min_weight_clause P0 P';
                N = map (\<lambda>D. (D, n)) (remdups (resolve_rename C C
                  @ concat (map (resolve_rename_either_way C \<circ> fst) Q)));
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
                 Q = filter (is_strictly_subsumed_by [C] \<circ> fst) Q;
                 P = filter (is_strictly_subsumed_by [C] \<circ> fst) P;
                 P = (C, i) # P
               in
                 (N, P, Q, n))))"

declare deterministic_RP_step.simps [simp del]

partial_function (option) deterministic_RP :: "'a dstate \<Rightarrow> 'a lclause list option" where
  "deterministic_RP St =
   (if is_final_dstate St then
      let (_, _, Q, _) = St in Some (map fst Q)
    else
      deterministic_RP (deterministic_RP_step St))"

lemma is_final_dstate_funpow_imp_deterministic_RP_neq_None:
  "is_final_dstate ((deterministic_RP_step ^^ k) St) \<Longrightarrow> deterministic_RP St \<noteq> None"
proof (induct k arbitrary: St)
  case (Suc k)
  note ih = this(1) and final_Sk = this(2)[simplified, unfolded funpow_swap1]
  show ?case
    using ih[OF final_Sk] by (subst deterministic_RP.simps) (simp add: prod.case_eq_if)
qed (subst deterministic_RP.simps, simp add: prod.case_eq_if)

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
      by (simp add: min_def) (use False eq_iff in fastforce)
    show ?thesis
      unfolding min by (rule ih[of Ci P0]) (simp add: ih[of Ci P1] ci False)
  qed
qed simp

lemma nonfinal_deterministic_RP_step:
  assumes
    nonfinal: "\<not> is_final_dstate St" and
    step: "St' = deterministic_RP_step St"
  shows "wstate_of_dstate St \<leadsto>\<^sub>w\<^sup>+ wstate_of_dstate St'"
proof -
  obtain N P Q :: "'a dclause list" and n :: nat where
    st: "St = (N, P, Q, n)"
    by (cases St) blast
  note step = step[unfolded st deterministic_RP_step.simps, simplified]

  show ?thesis
  proof (cases "List.find (\<lambda>(C, _). C = []) Q")
    case (Some Ci)
    show ?thesis
      sorry
  next
    case nil_ni_q: None
    note step = step[unfolded nil_ni_q, simplified]
    show ?thesis
    proof (cases "List.find (\<lambda>(C, _). C = []) P")
      case (Some Ci)
      then show ?thesis sorry
    next
      case nil_ni_p: None
      note step = step[unfolded nil_ni_p, simplified]
      show ?thesis
      proof (cases N)
        case n_nil: Nil
        note step = step[unfolded n_nil, simplified]
        show ?thesis
        proof (cases P)
          case Nil
          then have False
            using n_nil nonfinal[unfolded st] by (simp add: is_final_dstate.simps)
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

          define N' :: "'a dclause list" where
            "N' = map (\<lambda>D. (D, n))
               (remdups (resolve_rename C C @ concat (map (resolve_rename_either_way C \<circ> fst) Q)))"
          define P'' :: "'a dclause list" where
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
            apply (unfold wstate_of_dstate.simps)
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

        have "wstate_of_dstate ((E @ C, i) # N', P, Q, n)
           \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((E @ reduce (map fst P @ map fst Q) E C, i) # N', P, Q, n)" for E
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
            have "wstate_of_dstate ((E @ L # C, i) # N', P, Q, n)
              \<leadsto>\<^sub>w wstate_of_dstate ((E @ C, i) # N', P, Q, n)"
              by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
                    forward_reduction[of "mset D'" L' "mset (map (apfst mset) P)"
                      "mset (map (apfst mset) Q)" L \<sigma> "mset (E @ C)" "mset (map (apfst mset) N')" i n]])
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
          "wstate_of_dstate ((C, i) # N', P, Q, n) \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((C', i) # N', P, Q, n)"
          unfolding C'_def by (metis self_append_conv2)

        have proc_C: "wstate_of_dstate ((C', i) # N', P', Q', n')
          \<leadsto>\<^sub>w wstate_of_dstate (N', (C', i) # P', Q', n')" for P' Q' n'
          by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
                clause_processing[of "mset (map (apfst mset) N')" "mset C'" i
                  "mset (map (apfst mset) P')" "mset (map (apfst mset) Q')" n']],
              simp+)

        show ?thesis
        proof (cases "C' = []")
          case True
          note c'_nil = this
          note step = step[simplified c'_nil, simplified]

          have sub_P:
            "wstate_of_dstate (([], i) # N', P, Q, n) \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (([], i) # N', [], Q, n)"
            using nil_ni_q nil_ni_p
          proof (induct P)
            case (Cons P0 P)
            note ih = this(1) and nil_ni_q = this(2) and nil_ni_p0p = this(3)
            have nil_ni_p: "find (\<lambda>(C, _). C = []) P = None"
              using nil_ni_p0p by (auto split: if_splits)
            have "wstate_of_dstate (([], i) # N', P0 # P, Q, n)
              \<leadsto>\<^sub>w wstate_of_dstate (([], i) # N', P, Q, n)"
              by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
                    backward_subsumption_P[of "{#}" "mset (map (apfst mset) (([], i) # N'))"
                      "mset (fst P0)" "mset (map (apfst mset) P)" "snd P0" "mset (map (apfst mset) Q)"
                      n]],
                  cases P0, use nil_ni_q nil_ni_p0p in \<open>auto split: if_splits\<close>)
            then show ?case
              using ih[OF nil_ni_q nil_ni_p] by (rule converse_rtranclp_into_rtranclp)
          qed simp
          have sub_Q:
            "wstate_of_dstate (([], i) # N', [], Q, n) \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (([], i) # N', [], [], n)"
            using nil_ni_q
          proof (induct Q)
            case (Cons Q0 Q)
            note ih = this(1) and nil_ni_q0q = this(2)
            have nil_ni_q: "find (\<lambda>(C, _). C = []) Q = None"
              using nil_ni_q0q by (auto split: if_splits)
            have "wstate_of_dstate (([], i) # N', [], Q0 # Q, n)
              \<leadsto>\<^sub>w wstate_of_dstate (([], i) # N', [], Q, n)"
              by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
                    backward_subsumption_Q[of "{#}" "mset (map (apfst mset) (([], i) # N'))"
                      "mset (fst Q0)" "{#}" "mset (map (apfst mset) Q)" "snd Q0" n]],
                  cases Q0, use nil_ni_q0q in \<open>auto split: if_splits\<close>)
            then show ?case
              using ih[OF nil_ni_q] by (rule converse_rtranclp_into_rtranclp)
          qed simp
          have sub_N:
            "wstate_of_dstate (N', [([], i)], [], n) \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ([], [([], i)], [], n)"
          proof (induct N')
            case (Cons N'0 N')
            note ih = this
            have "wstate_of_dstate (N'0 # N', [([], i)], [], n)
              \<leadsto>\<^sub>w wstate_of_dstate (N', [([], i)], [], n)"
              by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
                    forward_subsumption[of "{#}" "{#({#}, i)#}" "{#}" "mset (fst N'0)"
                      "mset (map (apfst mset) N')" "snd N'0" n]])
                (cases N'0, auto)
            then show ?case
              using ih by (rule converse_rtranclp_into_rtranclp)
          qed simp
          have inf_C:
            "wstate_of_dstate ([], [([], i)], [], n) \<leadsto>\<^sub>w wstate_of_dstate ([], [], [([], i)], Suc n)"
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

            have "wstate_of_dstate ((C', i) # N', P, Q, n) \<leadsto>\<^sub>w wstate_of_dstate (N', P, Q, n)"
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
              then have "is_subsumed_by (map fst P @ map fst Q) C'"
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

            have red_Q: "wstate_of_dstate ((C', i) # N', P, Q, n)
              \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((C', i) # N', back_to_P @ P, Q', n)"
              sorry
            have red_P: "wstate_of_dstate ((C', i) # N', back_to_P @ P, Q', n)
              \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((C', i) # N', P', Q', n)"
              sorry
            have subs_Q: "wstate_of_dstate ((C', i) # N', P', Q', n)
              \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((C', i) # N', P', Q'', n)"
              sorry
            have subs_P: "wstate_of_dstate ((C', i) # N', P', Q'', n)
              \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((C', i) # N', P'', Q'', n)"
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
  qed
qed

lemma final_deterministic_RP_step: "is_final_dstate St \<Longrightarrow> deterministic_RP_step St = St"
  by (cases St) (auto simp: deterministic_RP_step.simps is_final_dstate.simps find_None_iff
      split: option.splits)

lemma deterministic_RP_SomeD:
  assumes "deterministic_RP (N, P, Q, n) = Some R"
  shows "\<exists>N' P' Q' n'. (\<exists>k. (deterministic_RP_step ^^ k) (N, P, Q, n) = (N', P', Q', n'))
    \<and> is_final_dstate (N', P', Q', n') \<and> R = map fst Q'"
proof (induct rule: deterministic_RP.raw_induct[OF _ assms])
  case (1 self_call St R)
  note ih = this(1) and step = this(2)

  obtain N P Q :: "'a dclause list" and n :: nat where
    st: "St = (N, P, Q, n)"
    by (cases St) blast
  note step = step[unfolded st, simplified]

  show ?case
  proof (cases "is_final_dstate (N, P, Q, n)")
    case True
    then have "(deterministic_RP_step ^^ 0) (N, P, Q, n) = (N, P, Q, n)
      \<and> is_final_dstate (N, P, Q, n) \<and> R = map fst Q"
      using step by simp
    then show ?thesis
      unfolding st by blast
  next
    case nonfinal: False
    note step = step[simplified nonfinal, simplified]

    obtain N' P' Q' n' k where
      "(deterministic_RP_step ^^ k) (deterministic_RP_step (N, P, Q, n)) = (N', P', Q', n')" and
      "is_final_dstate (N', P', Q', n')"
      "R = map fst Q'"
      using ih[OF step] by blast
    then show ?thesis
      unfolding st funpow_Suc_right[symmetric, THEN fun_cong, unfolded comp_apply] by blast
  qed
qed

lemma deterministic_RP_step_weighted_RP:
  "wstate_of_dstate St \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (deterministic_RP_step St)"
  by (cases "is_final_dstate St")
    (simp add: final_deterministic_RP_step nonfinal_deterministic_RP_step tranclp_into_rtranclp)+

lemma funpow_deterministic_RP_step_weighted_RP:
  "wstate_of_dstate St \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((deterministic_RP_step ^^ k) St)"
  by (induct k; simp) (meson deterministic_RP_step_weighted_RP rtranclp_trans)

lemma funpow_deterministic_RP_step_imp_weighted_RP:
  "(\<exists>k. (deterministic_RP_step ^^ k) St = St') \<Longrightarrow> wstate_of_dstate St \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate St'"
  using funpow_deterministic_RP_step_weighted_RP by blast

context
  fixes
    N0 :: "'a dclause list" and
    n0 :: nat and
    R :: "'a lclause list"
begin

abbreviation St0 :: "'a dstate" where
  "St0 \<equiv> (N0, [], [], n0)"

abbreviation grounded_N0 where
  "grounded_N0 \<equiv> grounding_of_clss (set (map (mset \<circ> fst) N0))"

abbreviation grounded_R :: "'a clause set" where
  "grounded_R \<equiv> grounding_of_clss (set (map mset R))"

primcorec derivation_from :: "'a dstate \<Rightarrow> 'a dstate llist" where
  "derivation_from St =
   LCons St (if is_final_dstate St then LNil else derivation_from (deterministic_RP_step St))"

abbreviation Sts :: "'a dstate llist" where
  "Sts \<equiv> derivation_from St0"

abbreviation gSts :: "'a wstate llist" where
  "gSts \<equiv> lmap wstate_of_dstate Sts"

lemma deriv_gSts_trancl_weighted_RP: "chain (op \<leadsto>\<^sub>w\<^sup>+) gSts"
proof -
  have "Sts' = derivation_from St0' \<Longrightarrow> chain (op \<leadsto>\<^sub>w\<^sup>+) (lmap wstate_of_dstate Sts')" for St0' Sts'
  proof (coinduction arbitrary: St0' Sts' rule: chain.coinduct)
    case chain
    note sts' = this
    show ?case
    proof (cases "is_final_dstate St0'")
      case True
      then have "ltl (lmap wstate_of_dstate Sts') = LNil"
        unfolding chain by simp
      then have "\<exists>St'. lmap wstate_of_dstate Sts' = LCons St' LNil"
        by (metis chain derivation_from.disc_iff lhd_LCons_ltl llist.map_disc_iff)
      then show ?thesis
        by blast
    next
      case nfinal: False
      have "lmap wstate_of_dstate Sts' =
        LCons (wstate_of_dstate St0') (lmap wstate_of_dstate (ltl Sts'))"
        unfolding sts' by (subst derivation_from.code) simp
      moreover have "ltl Sts' = derivation_from (deterministic_RP_step St0')"
        unfolding sts' using nfinal by (subst derivation_from.code) simp
      moreover have "wstate_of_dstate St0' \<leadsto>\<^sub>w\<^sup>+ wstate_of_dstate (lhd (ltl Sts'))"
        unfolding sts' using nonfinal_deterministic_RP_step[OF nfinal refl] nfinal
        by (subst derivation_from.code) simp
      ultimately show ?thesis
        by (metis (no_types) derivation_from.disc_iff derivation_from.simps(2) llist.map_sel(1))
    qed
  qed
  then show ?thesis
    by blast
qed

definition ssgSts :: "'a wstate llist" where
  "ssgSts = (SOME gSts'. chain (op \<leadsto>\<^sub>w) gSts' \<and> emb gSts gSts' \<and> (lfinite gSts' \<longleftrightarrow> lfinite gSts)
     \<and> lhd gSts' = lhd gSts \<and> llast gSts' = llast gSts)"

lemma ssgSts:
  "chain (op \<leadsto>\<^sub>w) ssgSts \<and> emb gSts ssgSts \<and> (lfinite ssgSts \<longleftrightarrow> lfinite gSts)
   \<and> lhd ssgSts = lhd gSts
   \<and> llast ssgSts = llast gSts"
  unfolding ssgSts_def
  by (rule someI_ex[OF chain_tranclp_imp_exists_chain[OF deriv_gSts_trancl_weighted_RP]])

lemmas deriv_ssgSts_weighted_RP = ssgSts[THEN conjunct1]
lemmas emb_ssgSts = ssgSts[THEN conjunct2, THEN conjunct1]
lemmas lfinite_ssgSts_iff = ssgSts[THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas lhd_ssgSts = ssgSts[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas llast_ssgSts = ssgSts[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]

lemma not_lnull_ssgSts: "\<not> lnull ssgSts"
  using deriv_ssgSts_weighted_RP by (cases rule: chain.cases) auto

lemma finite_ssgSts0: "finite (clss_of_wstate (lhd ssgSts))"
  unfolding lhd_ssgSts by (subst derivation_from.code) (simp add: clss_of_state_def)

lemma empty_ssgP0: "P_of_wstate (lhd ssgSts) = {}"
  unfolding lhd_ssgSts by (subst derivation_from.code) simp

lemma empty_ssgQ0: "Q_of_wstate (lhd ssgSts) = {}"
  unfolding lhd_ssgSts by (subst derivation_from.code) simp

lemma "clss_of_state (Liminf_wstate ssgSts) \<subseteq> clss_of_state (Liminf_wstate gSts)"
proof (cases "lfinite Sts")
  case fin: True
  show ?thesis
    by (rule equalityD1)
      (smt fin Liminf_state_fin chain_not_lnull[OF deriv_gSts_trancl_weighted_RP]
        lfinite_lmap[THEN iffD2] lfinite_ssgSts_iff[THEN iffD2] llast_lmap llast_ssgSts
        llist.map_disc_iff not_lnull_ssgSts)
next
  case False
  then show ?thesis
    using clss_of_Liminf_state_inf[OF _ emb_lmap[OF emb_ssgSts], of state_of_wstate] by simp
qed

abbreviation S_ssgQ :: "'a clause \<Rightarrow> 'a clause" where
  "S_ssgQ \<equiv> S_gQ ssgSts"

abbreviation ord_\<Gamma> :: "'a inference set" where
  "ord_\<Gamma> \<equiv> ground_resolution_with_selection.ord_\<Gamma> S_ssgQ"

abbreviation Rf :: "'a clause set \<Rightarrow> 'a clause set" where
  "Rf \<equiv> standard_redundancy_criterion.Rf"

abbreviation Ri :: "'a clause set \<Rightarrow> 'a inference set" where
  "Ri \<equiv> standard_redundancy_criterion.Ri ord_\<Gamma>"

abbreviation saturated_upto :: "'a clause set \<Rightarrow> bool" where
  "saturated_upto \<equiv> redundancy_criterion.saturated_upto ord_\<Gamma> Rf Ri"

context
  assumes drp_some: "deterministic_RP St0 = Some R"
begin

lemma lfinite_Sts: "lfinite Sts"
proof (induct rule: deterministic_RP.raw_induct[OF _ drp_some])
  case (1 self_call St St')
  note ih = this(1) and step = this(2)
  show ?case
    using step by (subst derivation_from.code, cases "is_final_dstate St", auto intro!: ih)
qed

lemma lfinite_gSts: "lfinite gSts"
  by (rule lfinite_lmap[THEN iffD2, OF lfinite_Sts])

lemmas lfinite_ssgSts = lfinite_ssgSts_iff[THEN iffD2, OF lfinite_gSts]

theorem
  deterministic_RP_saturated: "saturated_upto grounded_R" (is ?saturated) and
  deterministic_RP_model: "I \<Turnstile>s grounded_N0 \<longleftrightarrow> I \<Turnstile>s grounded_R" (is ?model)
proof -
  obtain N' P' Q' n' k where
    k_steps: "(deterministic_RP_step ^^ k) St0 = (N', P', Q', n')" (is "_ = ?Stk") and
    final: "is_final_dstate (N', P', Q', n')" and
    r: "R = map fst Q'"
    using deterministic_RP_SomeD[OF drp_some] by blast

  have wrp: "wstate_of_dstate St0 \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (llast Sts)"
    using chain_imp_rtranclp_lhd_llast
    by (metis (no_types) derivation_from.disc_iff derivation_from.simps(2) lfinite_Sts
        lfinite_gSts llast_lmap llist.map_sel(1) ssgSts)

  have last_sts: "llast Sts = ?Stk"
  proof -
    have "(deterministic_RP_step ^^ k') St0' = ?Stk \<Longrightarrow> llast (derivation_from St0') = ?Stk"
      for St0' k'
    proof (induct k' arbitrary: St0')
      case 0
      then show ?case
        using final by (subst derivation_from.code) simp
    next
      case (Suc k')
      note ih = this(1) and suc_k'_steps = this(2)
      show ?case
      proof (cases "is_final_dstate St0'")
        case True
        then show ?thesis
          using ih[of "deterministic_RP_step St0'"] suc_k'_steps final_deterministic_RP_step
            funpow_fixpoint[of deterministic_RP_step]
          by auto
      next
        case False
        then show ?thesis
          using ih[of "deterministic_RP_step St0'"] suc_k'_steps
          by (subst derivation_from.code) (simp add: llast_LCons funpow_swap1[symmetric])
      qed
    qed
    then show ?thesis
      using k_steps by blast
  qed

  have fin_gr_fgsts: "lfinite (lmap grounding_of_wstate ssgSts)"
    by (rule lfinite_lmap[THEN iffD2, OF lfinite_ssgSts])

  have lim_last: "Liminf_llist (lmap grounding_of_wstate ssgSts) =
    grounding_of_wstate (llast ssgSts)"
    unfolding lfinite_Liminf_llist[OF fin_gr_fgsts]
      llast_lmap[OF lfinite_ssgSts not_lnull_ssgSts]
    using not_lnull_ssgSts by simp

  have gr_st0: "grounding_of_wstate (wstate_of_dstate St0) = grounded_N0"
    by (simp add: clss_of_state_def comp_def)

  have "?saturated \<and> ?model"
  proof (cases "[] \<in> set R")
    case True
    have "{#} \<in> grounded_R"
      sorry

    have ?saturated
      sorry
    moreover have ?model
      sorry
    ultimately show ?thesis
      by blast
  next
    case nil_ni_r: False

    have gr_last: "grounding_of_wstate (llast ssgSts) = grounded_R"
      using nil_ni_r final unfolding r llast_ssgSts
      by (simp add: last_sts llast_lmap[OF lfinite_Sts] clss_of_state_def comp_def
          is_final_dstate.simps)
    then have gr_last_st: "grounding_of_wstate (wstate_of_dstate (llast Sts)) = grounded_R"
      by (simp add: lfinite_Sts llast_lmap llast_ssgSts)
    
    have ?saturated
      using weighted_RP_saturated[OF deriv_ssgSts_weighted_RP finite_ssgSts0 empty_ssgP0
          empty_ssgQ0, unfolded gr_last lim_last] by auto
    moreover have ?model
      by (rule rtranclp_imp_eq_image[of "op \<leadsto>\<^sub>w" "\<lambda>St. I \<Turnstile>s grounding_of_wstate St", OF _ wrp,
            unfolded gr_st0 gr_last_st])
        (use weighted_RP_model in blast)
    ultimately show ?thesis
      by blast
  qed
  then show ?saturated and ?model
    by blast+
qed

corollary deterministic_RP_refutation:
  "\<not> satisfiable grounded_N0 \<longleftrightarrow> {#} \<in> grounded_R" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then have "\<not> satisfiable grounded_R"
    unfolding true_clss_def true_cls_def by force
  then show ?lhs
    using deterministic_RP_model[THEN iffD1] by blast
next
  assume ?lhs
  then have "\<not> satisfiable grounded_R"
    using deterministic_RP_model[THEN iffD2] by blast
  then show ?rhs
    unfolding ord_\<Gamma>_saturated_upto_complete[OF deriv_ssgSts_weighted_RP finite_ssgSts0 empty_ssgP0
        empty_ssgQ0 deterministic_RP_saturated] .
qed

end

context
  assumes drp_none: "deterministic_RP St0 = None"
begin

theorem deterministic_RP_complete: "satisfiable grounded_N0"
proof (rule ccontr)
  assume unsat: "\<not> satisfiable grounded_N0"

  have unsat_gSts0: "\<not> satisfiable (grounding_of_wstate (lhd gSts))"
    using unsat
    sorry

  have bot_in_ss: "{#} \<in> Q_of_state (Liminf_wstate ssgSts)"
    by (rule weighted_RP_complete[OF deriv_ssgSts_weighted_RP finite_ssgSts0 empty_ssgP0
          empty_ssgQ0 unsat_gSts0[folded lhd_ssgSts]])
  have bot_in_lim: "{#} \<in> Q_of_state (Liminf_wstate gSts)"
  proof (cases "lfinite Sts")
    case fin: True
    have "Liminf_wstate ssgSts = Liminf_wstate gSts"
      by (rule Liminf_state_fin, simp_all add: fin lfinite_ssgSts_iff not_lnull_ssgSts,
          subst (1 2) llast_lmap,
          simp_all add: lfinite_ssgSts_iff fin not_lnull_ssgSts llast_ssgSts)
    then show ?thesis
      using bot_in_ss by simp
  next
    case False
    then show ?thesis
      using bot_in_ss Q_of_Liminf_state_inf[OF _ emb_lmap[OF emb_ssgSts]] by auto
  qed
  then obtain k where
    "{#} \<in> Q_of_wstate (lnth gSts k)"
    sorry
  then have emp_in: "{#} \<in> Q_of_state (state_of_dstate ((deterministic_RP_step ^^ k) St0))"
    sorry
  have "deterministic_RP St0 \<noteq> None"
    apply (rule is_final_dstate_funpow_imp_deterministic_RP_neq_None[of k])
    using emp_in
    apply (cases "(deterministic_RP_step ^^ k) St0")
    apply (fastforce simp: is_final_dstate.simps comp_def image_def)
    done
  then show False
    using drp_none ..
qed

end

end

end
