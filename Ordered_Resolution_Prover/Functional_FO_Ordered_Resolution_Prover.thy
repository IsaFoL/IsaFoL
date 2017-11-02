(*  Title:       A Functional Implementation of an Ordered Resolution Prover for First-Order Clauses
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>A Functional Implementation of an Ordered Resolution Prover for First-Order Clauses\<close>

text \<open>
This material is based on Section 4.3 (``A Simple Resolution Prover for First-Order Clauses) of 
Bachmair and Ganzinger's chapter. Specifically, it formalizes the prover in Figure 5 called
The Resolution Prover RP and its related lemmas and theorems including 
4.10, 4.11 and 4.13 (completeness of the prover).
\<close>

theory Functional_FO_Ordered_Resolution_Prover
  imports Fair_FO_Ordered_Resolution_Prover
begin

type_synonym 'a lclause = "'a literal list"
type_synonym 'a wlclause = "'a lclause \<times> nat"
type_synonym 'a wlstate =
  "'a wlclause list \<times> 'a wlclause list \<times> 'a wlclause list \<times> nat"

fun state_of_wlstate :: "'a wlstate \<Rightarrow> 'a state" where
  "state_of_wlstate (N, P, Q, _) =
   (set (map (mset \<circ> fst) N), set (map (mset \<circ> fst) P), set (map (mset \<circ> fst) Q))"

datatype 'a solution =
  Sat "'a lclause list"
| Unsat

context FO_resolution_prover_with_sum_product_weights
begin

abbreviation rtrancl_resolution_prover_with_weights (infix "\<leadsto>\<^sub>w\<^sup>*" 50) where
  "op \<leadsto>\<^sub>w\<^sup>* \<equiv> (op \<leadsto>\<^sub>w)\<^sup>*\<^sup>*"

(* FIXME: prove and move to right locale/file *)
lemma resolution_prover_with_weights_sound:
  "St \<leadsto>\<^sub>w St' \<Longrightarrow> I \<Turnstile>s grounding_of_state (state_of_wstate St) \<Longrightarrow>
   I \<Turnstile>s grounding_of_state (state_of_wstate St')"
  sorry

lemma rtrancl_resolution_prover_with_weights_sound:
  "St \<leadsto>\<^sub>w\<^sup>* St' \<Longrightarrow> I \<Turnstile>s grounding_of_state (state_of_wstate St) \<Longrightarrow>
   I \<Turnstile>s grounding_of_state (state_of_wstate St')"
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

fun
  select_clause :: "'a wlclause \<Rightarrow> 'a wlclause list \<Rightarrow> 'a wlclause"
where
  "select_clause (C, i) [] = (C, i)"
| "select_clause (C, i) ((D, j) # Ds) =
   select_clause (if weight (mset D, j) < weight (mset C, i) then (D, j) else (C, i)) Ds"

partial_function (option)
  deterministic_resolution_prover :: "'a wlstate \<Rightarrow> 'a solution option"
where
  "deterministic_resolution_prover St =
   (let
      (N, P, Q, n) = St
    in
      (case N of
         [] \<Rightarrow>
         (case P of
            [] \<Rightarrow> Some (Sat (map fst Q))
          | (C, i) # P' \<Rightarrow>
            let
              (C, i) = select_clause (C, i) P';
              P = remove1 (C, i) P;
              N = map (\<lambda>D. (D, Suc n)) (resolve C C @ concat (map (resolve_either_way C \<circ> fst) Q))
            in
              deterministic_resolution_prover (N, P, Q, Suc n))
       | (C, i) # N \<Rightarrow>
         let
           C = reduce (map fst (P @ Q)) [] C
         in
           if C = [] then
             Some Unsat
           else if is_tautology C \<or> is_subsumed_by (map fst (P @ Q)) C then
             deterministic_resolution_prover (N, P, Q, n)
           else
             let
               P = map (apfst (reduce [C])) P;
               P = filter (is_subsumed_by [C] \<circ> fst) N;
               Q = map (apfst (reduce [C])) Q;
               Q = filter (is_subsumed_by [C] \<circ> fst) N;
               P = (C, i) # P
             in
               deterministic_resolution_prover (N, P, Q, n)))"

lemma reduce_simulate_N:
  "(N \<union> {(mset (C @ C'), i)}, set (map (apfst mset) P), set (map (apfst mset) Q), n)
    \<leadsto>\<^sub>w\<^sup>* (N \<union> {(mset (C @ reduce (map fst (P @ Q)) C C'), i)}, set (map (apfst mset) P),
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
      using forward_reduction[of _ "set (map (apfst mset) P)" "set (map (apfst mset) Q)" L _ "mset (C @ C')" N i n]
      apply simp

      apply (rule forward_reduction)


      apply (rule rtranclp.transI)
      using 
      apply simp
      sorry
  next
    case False
    then show ?thesis
      using ih[of "L # C"] by simp
  qed
qed simp

(* FIXME
proof (induct "length (filter (\<lambda>L. is_reducible_lit (map fst (P @ Q)) C L) C)")
  case 0
  then have "length (reduce (map fst (P @ Q)) C) = length C"
    unfolding reduce_def using sum_length_filter_compl[of "is_reducible_lit (map fst (P @ Q)) C" C]
    by simp
  then have "reduce (map fst (P @ Q)) C = C"
    unfolding reduce_def  by (metis filter_True length_filter_less less_irrefl)
  then show ?case
    by simp
next
  case (Suc k)

  let ?is_red = "is_reducible_lit (map fst (P @ Q)) C"

  let ?D = "takeWhile (\<lambda>L. \<not> ?is_red L) C"
  let ?E = "dropWhile (\<lambda>L. \<not> ?is_red L) C"


  term List.extract

  thm split_list_first[of _ "filter ?is_red C"]

  then show ?case
    sorry
qed
*)
  sorry

theorem deterministic_resolution_prover_sound_unsat:
  assumes
    su: "deterministic_resolution_prover St = Some sol" and
    sol_unsat: "sol = Unsat"
  shows "\<not> satisfiable (grounding_of_state (state_of_wlstate St))"
  using sol_unsat
proof (induct rule: deterministic_resolution_prover.raw_induct[OF _ su])
  case (1 self_call St sol)
  note ih = this(1)[OF _ refl] and call = this(2) and sol_unsat = this(3)

  obtain N P Q :: "'a wlclause list" and n :: nat where
    st: "St = (N, P, Q, n)"
    by (cases St) blast

  note ih = ih[unfolded st]
  note call = call[unfolded sol_unsat st, simplified]

  show ?case
  proof (cases N)
    case n_nil: Nil
    note call = call[unfolded n_nil, simplified]
    show ?thesis
    proof (cases P)
      case p_nil: Nil
      note call = call[unfolded p_nil, simplified]
      show ?thesis
        using call by simp
    next
      case p_cons: (Cons Ci P')
      note call = call[unfolded p_cons, simplified]

      obtain C :: "'a lclause" and i :: nat where
        pick: "select_clause Ci P' = (C, i)"
        by (cases "select_clause Ci P'") simp
      note call = call[unfolded pick, simplified, folded remove1.simps(2)]

      show ?thesis
        apply (rule contrapos_nn[OF ih[OF call]])
        apply (auto simp: comp_def simp del: remove1.simps(2))


        sorry
    qed
  next
    case n_cons: (Cons Ci N')
    note call = call[unfolded n_cons, simplified]

    obtain C :: "'a lclause" and i :: nat where
      ci: "Ci = (C, i)"
      by (cases Ci) simp
    note call = call[unfolded ci, simplified]

    define C' :: "'a lclause" where
      "C' = reduce (map fst P @ map fst Q) [] C"
    note call = call[unfolded ci C'_def[symmetric], simplified]

    show ?thesis
    proof (cases "C' = Nil")
      case c'_nil: True
      show ?thesis
      proof (rule; erule exE)
        fix I
        assume "I \<Turnstile>s grounding_of_state (state_of_wlstate St)"
        then show False
          unfolding st n_cons ci
          using c'_nil[unfolded C'_def]
            rtrancl_resolution_prover_with_weights_sound[OF reduce_simulate_N,
              of I "set (map (apfst mset) N')" "[]" C i P Q n]
          by (simp add: clss_of_state_def grounding_of_clss_def)
      qed
    next
      case c'_nnil: False
      note call = call[simplified c'_nnil, simplified]
      show ?thesis
      proof (cases "is_tautology C' \<or> is_subsumed_by (map fst P @ map fst Q) C'")
        case taut_or_subs: True
        note call = call[simplified taut_or_subs, simplified]
        show ?thesis
          unfolding st n_cons ci using ih[OF call]
          by (auto simp: clss_of_state_def grounding_of_clss_def)
      next
        case not_taut_or_subs: False
        note call = call[simplified not_taut_or_subs, simplified]
        show ?thesis
          unfolding st n_cons ci
          using ih[OF call]
          (* use soundness of subsumption at calculus level *)
          sorry
      qed
    qed
  qed
qed

thm
  deterministic_resolution_prover.fixp_induct
  deterministic_resolution_prover.raw_induct
  deterministic_resolution_prover.mono
  deterministic_resolution_prover.simps

(*
  using su
  apply (induct rule: deterministic_resolution_prover.fixp_induct)
*)

end

end
