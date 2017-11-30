(*  Title:       A Deterministic Ordered Resolution Prover for First-Order Clauses
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>A Deterministic Ordered Resolution Prover for First-Order Clauses\<close>

text \<open>
TODO.
\<close>

theory Deterministic_FO_Ordered_Resolution_Prover
  imports Polynomial_Factorization.Missing_List Weighted_FO_Ordered_Resolution_Prover
begin


section \<open>Library\<close>

lemma apfst_fst_snd: "apfst f x = (f (fst x), snd x)"
  by (rule apfst_conv[of _ "fst x" "snd x" for x, unfolded prod.collapse])

lemma apfst_comp_rpair_const: "apfst f \<circ> (\<lambda>x. (x, y)) = (\<lambda>x. (x, y)) \<circ> f"
  by (simp add: comp_def)

lemma map_filter_neq_eq_filter_map:
  "map f (filter (\<lambda>y. f x \<noteq> f y) xs) = filter (\<lambda>z. f x \<noteq> z) (map f xs)"
  by (induct xs) auto

lemma mset_map_remdups_gen:
  "mset (map f (remdups_gen f xs)) = mset (remdups_gen (\<lambda>x. x) (map f xs))"
  by (induct f xs rule: remdups_gen.induct) (auto simp: map_filter_neq_eq_filter_map)

lemma mset_remdups_gen_ident: "mset (remdups_gen (\<lambda>x. x) xs) = mset_set (set xs)"
proof -
  have "f = (\<lambda>x. x) \<Longrightarrow> mset (remdups_gen f xs) = mset_set (set xs)" for f
  proof (induct f xs rule: remdups_gen.induct)
    case (2 f x xs)
    note ih = this(1) and f = this(2)
    show ?case
      unfolding f remdups_gen.simps ih[OF f, unfolded f] mset.simps
      by (metis finite_set list.simps(15) mset_set.insert_remove removeAll_filter_not_eq
          remove_code(1) remove_def)
  qed simp
  then show ?thesis
    by simp
qed

(* FIXME: clone of Lambda_Free_RPOs *)
lemma wf_app: "wf r \<Longrightarrow> wf {(x, y). (f x, f y) \<in> r}"
  unfolding wf_eq_minimal by (intro allI, drule spec[of _ "f ` Q" for Q]) auto

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

definition subsume :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> bool" where
  "subsume Ds C \<longleftrightarrow> (\<exists>D \<in> set Ds. subsumes (mset D) (mset C))"

definition strictly_subsume :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> bool" where
  "strictly_subsume Ds C \<longleftrightarrow> (\<exists>D \<in> set Ds. strictly_subsumes (mset D) (mset C))"

definition is_reducible_lit :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> 'a literal \<Rightarrow> bool" where
  "is_reducible_lit Ds C L \<longleftrightarrow>
   (\<exists>D \<in> set Ds. \<exists>L' \<in> set D. \<exists>\<sigma>. - L = L' \<cdot>l \<sigma> \<and> mset (remove1 L' D) \<cdot> \<sigma> \<subseteq># mset C)"

primrec reduce :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause" where
  "reduce _ _ [] = []"
| "reduce Ds C (L # C') =
   (if is_reducible_lit Ds (C @ C') L then reduce Ds C C' else L # reduce Ds (L # C) C')"

definition reduce_all :: "'a lclause list \<Rightarrow> 'a dclause list \<Rightarrow> 'a dclause list" where
  "reduce_all Ds = map (apfst (reduce Ds []))"

fun reduce_all2 :: "'a lclause list \<Rightarrow> 'a dclause list \<Rightarrow> 'a dclause list \<times> 'a dclause list" where
  "reduce_all2 _ [] = ([], [])"
| "reduce_all2 Ds (Ci # Cs) =
   (let
      (C, i) = Ci;
      C' = reduce Ds [] C
    in
      (if C' = C then apsnd else apfst) (Cons (C', i)) (reduce_all2 Ds Cs))"

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

definition resolve_rename :: "'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause list" where
  "resolve_rename C D =
   (let \<sigma>s = renamings_apart [mset D, mset C] in
      resolve (map (\<lambda>L. L \<cdot>l last \<sigma>s) C) (map (\<lambda>L. L \<cdot>l hd \<sigma>s) D))"

definition resolve_rename_either_way :: "'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause list" where
  "resolve_rename_either_way C D = resolve_rename C D @ resolve_rename D C"

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
         Some Ci \<Rightarrow> ([], [], P @ Q, n + length P)
       | None \<Rightarrow>
         (case N of
           [] \<Rightarrow>
           (case P of
              [] \<Rightarrow> (N, P, Q, n)
            | P0 # P' \<Rightarrow>
              let
                (C, i) = select_min_weight_clause P0 P';
                N = map (\<lambda>D. (D, n)) (remdups_gen mset (resolve_rename C C @
                  concat (map (resolve_rename_either_way C \<circ> fst) Q)));
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
             else if is_tautology C \<or> subsume (map fst (P @ Q)) C then
               (N, P, Q, n)
             else
               let
                 (back_to_P, Q) = reduce_all2 [C] Q;
                 P = back_to_P @ P;
                 P = reduce_all [C] P;
                 Q = filter (Not \<circ> strictly_subsume [C] \<circ> fst) Q;
                 P = filter (Not \<circ> strictly_subsume [C] \<circ> fst) P;
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

lemma reduce_mset_eq: "mset C = mset C' \<Longrightarrow> reduce Ds C E = reduce Ds C' E"
proof (induct E arbitrary: C C')
  case (Cons L E)
  note ih = this(1) and mset_eq = this(2)
  have mset_eq': "mset (L # C) = mset (L # C')"
    using mset_eq by simp
  have red_iff: "is_reducible_lit Ds (C @ E) L \<longleftrightarrow> is_reducible_lit Ds (C' @ E) L"
    by (simp add: mset_eq is_reducible_lit_def)
  show ?case
    using ih[OF mset_eq] ih[OF mset_eq'] by (simp add: red_iff)
qed simp

lemma reduce_rotate[simp]: "reduce Ds (C @ [L]) E = reduce Ds (L # C) E"
  by (rule reduce_mset_eq) simp

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

lemma empty_N_if_Nil_in_P_or_Q:
  assumes nil_in: "[] \<in> fst ` set (P @ Q)"
  shows "wstate_of_dstate (N, P, Q, n) \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ([], P, Q, n)"
proof (induct N)
  case ih: (Cons N0 N)
  have "wstate_of_dstate (N0 # N, P, Q, n) \<leadsto>\<^sub>w wstate_of_dstate (N, P, Q, n)"
    by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
          wrp.forward_subsumption[of "{#}" "mset (map (apfst mset) P)" "mset (map (apfst mset) Q)"
            "mset (fst N0)" "mset (map (apfst mset) N)" "snd N0" n]])
      (use nil_in in \<open>force simp: image_def apfst_fst_snd\<close>)+
  then show ?case
    using ih by (rule converse_rtranclp_into_rtranclp)
qed simp

lemma remove_strictly_subsumed_clauses_in_P:
  assumes c_in: "C \<in> fst ` set N"
  shows "wstate_of_dstate (N, P @ P', Q, n)
    \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, P @ filter (Not \<circ> strictly_subsume [C] \<circ> fst) P', Q, n)"
proof (induct P' arbitrary: P)
  case ih: (Cons Dk P')
  have "wstate_of_dstate (N, P @ Dk # P', Q, n) \<leadsto>\<^sub>w\<^sup>*
    wstate_of_dstate (N, P @ filter (Not \<circ> strictly_subsume [C] \<circ> fst) [Dk] @ P', Q, n)"
  proof (cases "strictly_subsume [C] (fst Dk)")
    case subs: True
    have "wstate_of_dstate (N, P @ Dk # P', Q, n) \<leadsto>\<^sub>w wstate_of_dstate (N, P @ P', Q, n)"
      by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
            wrp.backward_subsumption_P[of "mset C" "mset (map (apfst mset) N)" "mset (fst Dk)"
              "mset (map (apfst mset) (P @ P'))" "snd Dk" "mset (map (apfst mset) Q)" n]])
        (use c_in subs in \<open>auto simp: apfst_fst_snd strictly_subsume_def\<close>)
    then show ?thesis
      by auto
  qed simp
  then show ?case
    using ih[of "P @ filter (Not \<circ> strictly_subsume [C] \<circ> fst) [Dk]"] by force
qed simp

lemma remove_strictly_subsumed_clauses_in_Q:
  assumes c_in: "C \<in> fst ` set N"
  shows "wstate_of_dstate (N, P, Q @ Q', n)
    \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, P, Q @ filter (Not \<circ> strictly_subsume [C] \<circ> fst) Q', n)"
proof (induct Q' arbitrary: Q)
  case ih: (Cons Dk Q')
  have "wstate_of_dstate (N, P, Q @ Dk # Q', n) \<leadsto>\<^sub>w\<^sup>*
    wstate_of_dstate (N, P, Q @ filter (Not \<circ> strictly_subsume [C] \<circ> fst) [Dk] @ Q', n)"
  proof (cases "strictly_subsume [C] (fst Dk)")
    case subs: True
    have "wstate_of_dstate (N, P, Q @ Dk # Q', n) \<leadsto>\<^sub>w wstate_of_dstate (N, P, Q @ Q', n)"
      by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
            wrp.backward_subsumption_Q[of "mset C" "mset (map (apfst mset) N)" "mset (fst Dk)"
              "mset (map (apfst mset) P)" "mset (map (apfst mset) (Q @ Q'))" "snd Dk" n]])
        (use c_in subs in \<open>auto simp: apfst_fst_snd strictly_subsume_def\<close>)
    then show ?thesis
      by auto
  qed simp
  then show ?case
    using ih[of "Q @ filter (Not \<circ> strictly_subsume [C] \<circ> fst) [Dk]"] by force
qed simp

lemma reduce_clause_in_P:
  assumes c_in: "C \<in> fst ` set N"
  shows "wstate_of_dstate (N, P @ (D @ D', k) # P', Q, n)
    \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, P @ (D @ reduce [C] D D', k) # P', Q, n)"
proof (induct D' arbitrary: D)
  case ih: (Cons L D')
  show ?case
  proof (cases "is_reducible_lit [C] (D @ D') L")
    case red: True
    then obtain L' :: "'a literal" and \<sigma> :: 's where
      l'_in: "L' \<in> set C" and
      not_l: "- L = L' \<cdot>l \<sigma>" and
      subs: "mset (remove1 L' C) \<cdot> \<sigma> \<subseteq># mset (D @ D')"
      unfolding is_reducible_lit_def by force

    have "wstate_of_dstate (N, P @ (D @ L # D', k) # P', Q, n)
      \<leadsto>\<^sub>w wstate_of_dstate (N, P @ (D @ D', k) # P', Q, n)"
      by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
            wrp.backward_reduction_P[of "mset C - {#L'#}" L' "mset (map (apfst mset) N)" L \<sigma>
              "mset (D @ D')" "mset (map (apfst mset) (P @ P'))" k "mset (map (apfst mset) Q)" n]],
          use l'_in not_l subs c_in in auto)
    then show ?thesis
      using ih[of D] red by simp
  next
    case False
    then show ?thesis
      using ih[of "D @ [L]"] by simp
  qed
qed simp

lemma reduce_clause_in_Q:
  assumes
    c_in: "C \<in> fst ` set N" and
    d'_red: "reduce [C] D D' \<noteq> D'"
  shows "wstate_of_dstate (N, P, Q @ (D @ D', k) # Q', n)
    \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, (D @ reduce [C] D D', k) # P, Q @ Q', n)"
  using d'_red
proof (induct D' arbitrary: D)
  case (Cons L D')
  note ih = this(1) and ld'_red = this(2)
  then show ?case
  proof (cases "is_reducible_lit [C] (D @ D') L")
    case red: True
    then obtain L' :: "'a literal" and \<sigma> :: 's where
      l'_in: "L' \<in> set C" and
      not_l: "- L = L' \<cdot>l \<sigma>" and
      subs: "mset (remove1 L' C) \<cdot> \<sigma> \<subseteq># mset (D @ D')"
      unfolding is_reducible_lit_def by force

    have "wstate_of_dstate (N, P, Q @ (D @ L # D', k) # Q', n)
      \<leadsto>\<^sub>w wstate_of_dstate (N, (D @ D', k) # P, Q @ Q', n)"
      by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
            wrp.backward_reduction_Q[of "mset C - {#L'#}" L' "mset (map (apfst mset) N)" L \<sigma>
              "mset (D @ D')" "mset (map (apfst mset) P)" "mset (map (apfst mset) (Q @ Q'))" k n]],
          use l'_in not_l subs c_in in auto)
    then show ?thesis
      using red reduce_clause_in_P[OF c_in, of "[]" D D' k P "Q @ Q'" n] by simp
  next
    case l_nred: False
    then have d'_red: "reduce [C] (D @ [L]) D' \<noteq> D'"
      using ld'_red by simp
    show ?thesis
      using ih[OF d'_red] l_nred by simp
  qed
qed simp

lemma reduce_clauses_in_P:
  assumes c_in: "C \<in> fst ` set N"
  shows "wstate_of_dstate (N, P @ P', Q, n) \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, P @ reduce_all [C] P', Q, n)"
  unfolding reduce_all_def
proof (induct P' arbitrary: P)
  case ih: (Cons Dk P')
  have "wstate_of_dstate (N, P @ Dk # P', Q, n)
     \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, P @ apfst (reduce [C] []) Dk # P', Q, n)"
    by (cases Dk, simp only: apfst_conv,
        rule reduce_clause_in_P[of _ _  _"[]", unfolded append_Nil, OF c_in])
  then show ?case
    using ih[of "P @ [apfst (reduce [C] []) Dk]"] by force
qed simp

lemma reduce_clauses_in_Q:
  assumes c_in: "C \<in> fst ` set N"
  shows "wstate_of_dstate (N, P, Q @ Q', n)
    \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, fst (reduce_all2 [C] Q') @ P, Q @ snd (reduce_all2 [C] Q'), n)"
proof (induct Q' arbitrary: P Q)
  case ih: (Cons Dk Q')
  show ?case
  proof (cases "reduce [C] [] (fst Dk) = fst Dk")
    case True
    then show ?thesis
      using ih[of _ "Q @ [Dk]"] by (simp add: case_prod_beta)
  next
    case red: False
    have "wstate_of_dstate (N, P, Q @ Dk # Q', n)
      \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, (reduce [C] [] (fst Dk), snd Dk) # P, Q @ Q', n)"
      using reduce_clause_in_Q[of _ _ _ _ _ "[]" _ "Q @ Q'", OF c_in red] by (cases Dk) force
    then show ?thesis
      using red ih[of "(reduce [C] [] (fst Dk), snd Dk) # P" Q]
      by (fastforce simp: case_prod_beta)
  qed
qed simp

abbreviation Bin_ord_resolve :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> 'a clause set" where
  "Bin_ord_resolve C D \<equiv> {E. \<exists>AAs As \<sigma>. ord_resolve S [C] D AAs As \<sigma> E}"

abbreviation Bin_ord_resolve_rename :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> 'a clause set" where
  "Bin_ord_resolve_rename C D \<equiv> {E. \<exists>AAs As \<sigma>. ord_resolve_rename S [C] D AAs As \<sigma> E}"

lemma resolve_eq_Bin_ord_resolve:
  "mset ` set (resolve C D) = Bin_ord_resolve (mset C) (mset D)"
  sorry (* hard *)

lemma resolve_rename_eq_Bin_ord_resolve_rename:
  "mset ` set (resolve_rename C D) = Bin_ord_resolve_rename (mset C) (mset D)"
  unfolding resolve_rename_def ord_resolve_rename.simps Let_def resolve_eq_Bin_ord_resolve
  apply auto
  sorry (* not too bad *)

lemma ord_resolve_one_side_prem: "ord_resolve S CAs DA AAs As \<sigma> E \<Longrightarrow> length CAs = 1"
  apply (erule ord_resolve.cases)
  unfolding eligible.simps S_empty by force

lemma ord_resolve_rename_one_side_prem: "ord_resolve_rename S CAs DA AAs As \<sigma> E \<Longrightarrow> length CAs = 1"
  apply (erule ord_resolve_rename.cases)
  apply (drule ord_resolve_one_side_prem)
  apply (hypsubst)
  apply simp
  apply (unfold renames_apart[THEN conjunct1])
  apply simp
  done

lemma ord_FO_\<Gamma>_side_prem: 
  assumes \<gamma>_in: "\<gamma> \<in> ord_FO_\<Gamma> S"
  shows "side_prems_of \<gamma> = {#THE D. D \<in># side_prems_of \<gamma>#}"
  sorry

lemma ord_FO_\<Gamma>_infer_from_Collect_eq:
  "{\<gamma> \<in> ord_FO_\<Gamma> S. infer_from (DD \<union> {C}) \<gamma> \<and> C \<in># prems_of \<gamma>} =
   {\<gamma> \<in> ord_FO_\<Gamma> S. \<exists>D \<in> DD \<union> {C}. prems_of \<gamma> = {#C, D#}}"
  unfolding infer_from_def
  apply (rule set_eq_subset[THEN iffD2])
  apply (rule conjI)
   apply clarify
   apply (subst (asm) (1 2) ord_FO_\<Gamma>_side_prem, assumption, assumption)
   apply (subst (1) ord_FO_\<Gamma>_side_prem, assumption)
   apply auto[1]
  apply clarify
  apply (subst (asm) (1) ord_FO_\<Gamma>_side_prem, assumption)
  apply (subst (1 2) ord_FO_\<Gamma>_side_prem, assumption)
  apply auto
  done

lemma inferences_between_eq_UNION: "inference_system.inferences_between (ord_FO_\<Gamma> S) Q C =
  inference_system.inferences_between (ord_FO_\<Gamma> S) {C} C
  \<union> (\<Union>D \<in> Q. inference_system.inferences_between (ord_FO_\<Gamma> S) {D} C)"
  unfolding ord_FO_\<Gamma>_infer_from_Collect_eq inference_system.inferences_between_def by auto

lemma concls_of_inferences_between_singleton_eq_Bin_ord_resolve_rename:
  "concls_of (inference_system.inferences_between (ord_FO_\<Gamma> S) {D} C) =
   Bin_ord_resolve_rename C C \<union> Bin_ord_resolve_rename C D \<union> Bin_ord_resolve_rename D C"
  unfolding inference_system.inferences_between_def ord_FO_\<Gamma>_infer_from_Collect_eq
  unfolding ord_FO_\<Gamma>_def infer_from_def
  apply auto
  sorry (* easy *)

lemma concls_of_inferences_between_eq_Bin_ord_resolve_rename:
  "concls_of (inference_system.inferences_between (ord_FO_\<Gamma> S) Q C) =
   Bin_ord_resolve_rename C C \<union> (\<Union>D \<in> Q. Bin_ord_resolve_rename C D \<union> Bin_ord_resolve_rename D C)"
  by (subst inferences_between_eq_UNION)
    (auto simp: image_Un image_UN concls_of_inferences_between_singleton_eq_Bin_ord_resolve_rename)

lemma resolve_rename_either_way_eq_congls_of_inferences_between:
  "mset ` set (resolve_rename C C) \<union> (\<Union>D \<in> Q. mset ` set (resolve_rename_either_way C D)) =
   concls_of (inference_system.inferences_between (ord_FO_\<Gamma> S) (mset ` Q) (mset C))"
  unfolding resolve_rename_either_way_def
  apply (simp add: image_Un UN_Un_distrib)
  unfolding resolve_rename_eq_Bin_ord_resolve_rename
    concls_of_inferences_between_eq_Bin_ord_resolve_rename
  apply (simp add: UN_Un_distrib)
  done

lemma compute_inferences:
  assumes
    ci_in: "(C, i) \<in> set P" and
    ci_min: "\<forall>(D, j) \<in># mset (map (apfst mset) P). weight (mset C, i) \<le> weight (D, j)"
  shows
    "wstate_of_dstate ([], P, Q, n) \<leadsto>\<^sub>w
     wstate_of_dstate (map (\<lambda>D. (D, n)) (remdups_gen mset (resolve_rename C C @
         concat (map (resolve_rename_either_way C \<circ> fst) Q))),
       remove1 (C, i) P, (C, i) # Q, Suc n)" (is "_ \<leadsto>\<^sub>w wstate_of_dstate (?N, _)")
proof -
  have ms_ci_in: "(mset C, i) \<in># image_mset (apfst mset) (mset P)"
    using ci_in by force

  show ?thesis
    apply (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
          wrp.inference_computation[of "mset (map (apfst mset) P) - {#(mset C, i)#}" "mset C" i
            "mset (map (apfst mset) ?N)" n "mset (map (apfst mset) Q)"]])
       apply (simp add: add_mset_remove_trivial_eq[THEN iffD2, OF ms_ci_in, symmetric])
      apply auto[1]
    using ms_ci_in
      apply (simp add: ci_in image_mset_remove1_mset_if)
    using ci_min
     apply (meson in_diffD)
    apply (simp only: list.map_comp apfst_comp_rpair_const)
    apply (simp only: list.map_comp[symmetric])
    apply (subst mset_map)
    apply (unfold mset_map_remdups_gen mset_remdups_gen_ident)
    apply (subst image_mset_mset_set)
     apply (simp add: inj_on_def)
    apply (subst mset_set_eq_iff)
      apply simp
    apply (simp add: finite_ord_FO_resolution_inferences_between)
    apply (rule arg_cong[of _ _ "\<lambda>N. (\<lambda>D. (D, n)) ` N"])

    apply (simp only: map_concat list.map_comp image_comp)
    using resolve_rename_either_way_eq_congls_of_inferences_between[of C "fst ` set Q", symmetric]
    apply (simp only: image_comp comp_def)
    apply (simp add: image_UN)
    done
qed

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
    case ci: (Some Ci)
    note step = step[unfolded ci, simplified]
    then have st_st': "St = St'"
      using st by simp
    have "is_final_dstate St"
      unfolding st_st' step is_final_dstate.simps
      using option.discI[OF ci, unfolded find_None_iff, simplified] by force
    then have False
      using nonfinal by satx
    then show ?thesis
      ..
  next
    case nil_ni_q: None
    note step = step[unfolded nil_ni_q, simplified]
    show ?thesis
    proof (cases "List.find (\<lambda>(C, _). C = []) P")
      case ci: (Some Ci)
      note step = step[unfolded ci, simplified]

      have "[] \<in> fst ` set (P @ Q) \<Longrightarrow>
        wstate_of_dstate (N, P, Q, n) \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ([], [], P @ Q, n + length P)"
      proof (induct "length P" arbitrary: N P Q n)
        case 0
        note len_p = this(1) and nil_in = this(2)

        have p: "P = []"
          using len_p by simp
        have "wstate_of_dstate (N, [], Q, n) \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ([], [], Q, n)"
          by (rule empty_N_if_Nil_in_P_or_Q[OF nil_in[unfolded p]])
        then show ?case
          unfolding p by simp
      next
        case (Suc k)
        note ih = this(1) and len_p = this(2) and nil_in = this(3)

        obtain Ci0 :: "'a dclause" where
          ci0: "Ci0 \<in> set P"
          using len_p by (metis Suc_length_conv list.set_intros(1))
        obtain C :: "'a lclause" and i :: nat where
          ci_in: "(C, i) \<in> set P" and
          ci_min: "\<forall>(D, j) \<in> set P. weight (mset C, i) \<le> weight (mset D, j)"
          using wf_eq_minimal[THEN iffD1, OF wf_app[OF wf, simplified],
              of "\<lambda>(C, i). weight (mset C, i)", rule_format, OF ci0]
          by force

        have mset: "mset (remove1 (C, i) P @ (C, i) # Q) = mset (P @ Q)"
          using ci_in by simp

        have "wstate_of_dstate (N, P, Q, n) \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ([], P, Q, n)"
          by (rule empty_N_if_Nil_in_P_or_Q[OF nil_in])
        also obtain N' :: "'a dclause list" where
          "\<dots> \<leadsto>\<^sub>w wstate_of_dstate (N', remove1 (C, i) P, (C, i) # Q, Suc n)"
          by (atomize_elim, rule exI, rule compute_inferences[OF ci_in], use ci_min in fastforce)
        also have "\<dots> \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ([], [], remove1 (C, i) P @ (C, i) # Q, n + length P)"
        proof -
          have k: "k = length (remove1 (C, i) P)"
            using ci_in len_p by (metis One_nat_def diff_Suc_Suc length_remove1 minus_nat.diff_0)
          moreover have "Suc n + length (remove1 (C, i) P) = n + length P"
            using ci_in k len_p by simp
          ultimately show ?thesis
            using ih[of "remove1 (C, i) P" "(C, i) # Q" N' "Suc n"] mset[THEN mset_eq_setD] nil_in
            by presburger
        qed
        also have "\<dots> = wstate_of_dstate ([], [], P @ Q, n + length P)"
          unfolding wstate_of_dstate.simps mset_map mset ..
        finally show ?case
          .
      qed
      then show ?thesis
        unfolding st step using option.discI[OF ci, unfolded find_None_iff]
        by (force dest!: rtranclpD)
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

          show ?thesis
            unfolding st n_nil step p_cons[symmetric] ci[symmetric] prod.case
            by (rule tranclp.r_into_trancl, rule compute_inferences[OF ci_in])
              (simp add: select_min_weight_clause_min_weight[OF ci, simplified] p_cons)
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
            obtain D D' :: "'a literal list" and L' :: "'a literal" and \<sigma> :: 's where
              "D \<in> set (map fst P @ map fst Q)" and
              "D' = remove1 L' D" and
              "L' \<in> set D" and
              "- L = L' \<cdot>l \<sigma>" and
              "mset D' \<cdot> \<sigma> \<subseteq># mset (E @ C)"
              using l_red unfolding is_reducible_lit_def comp_def by blast
            then have \<sigma>:
              "mset D' + {#L'#} \<in> set (map (mset \<circ> fst) (P @ Q))"
              "- L = L' \<cdot>l \<sigma> \<and> mset D' \<cdot> \<sigma> \<subseteq># mset (E @ C)"
              unfolding is_reducible_lit_def by (auto simp: comp_def)
            have "wstate_of_dstate ((E @ L # C, i) # N', P, Q, n)
              \<leadsto>\<^sub>w wstate_of_dstate ((E @ C, i) # N', P, Q, n)"
              by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
                    wrp.forward_reduction[of "mset D'" L' "mset (map (apfst mset) P)"
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
                wrp.clause_processing[of "mset (map (apfst mset) N')" "mset C'" i
                  "mset (map (apfst mset) P')" "mset (map (apfst mset) Q')" n']],
              simp+)

        show ?thesis
        proof (cases "C' = []")
          case True
          note c'_nil = this
          note step = step[simplified c'_nil, simplified]

          have filter_p: "filter (Not \<circ> strictly_subsume [[]] \<circ> fst) P = []"
            using nil_ni_p unfolding strictly_subsume_def filter_empty_conv find_None_iff by force
          have filter_q: "filter (Not \<circ> strictly_subsume [[]] \<circ> fst) Q = []"
            using nil_ni_q unfolding strictly_subsume_def filter_empty_conv find_None_iff by force

          note red_C[unfolded c'_nil]
          also have "wstate_of_dstate (([], i) # N', P, Q, n)
            \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (([], i) # N', [], Q, n)"
            by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w\<^sup>*", OF _ _
                    remove_strictly_subsumed_clauses_in_P[of "[]" _ "[]", unfolded append_Nil],
                  OF refl])
              (auto simp: filter_p)
          also have "\<dots> \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (([], i) # N', [], [], n)"
            by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w\<^sup>*", OF _ _
                    remove_strictly_subsumed_clauses_in_Q[of "[]" _ _ "[]", unfolded append_Nil],
                  OF refl])
              (auto simp: filter_q)
          also note proc_C[unfolded c'_nil, THEN tranclp.r_into_trancl[of "op \<leadsto>\<^sub>w"]]
          also have "wstate_of_dstate (N', [([], i)], [], n)
            \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ([], [([], i)], [], n)"
            by (rule empty_N_if_Nil_in_P_or_Q) simp
          also have "\<dots> \<leadsto>\<^sub>w wstate_of_dstate ([], [], [([], i)], Suc n)"
            by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
                  wrp.inference_computation[of "{#}" "{#}" i "{#}" n "{#}"]])
              (auto simp: ord_FO_resolution_inferences_between_empty_empty)
          finally show ?thesis
            unfolding step st n_cons ci .
        next
          case c'_nnil: False
          note step = step[simplified c'_nnil, simplified]
          show ?thesis
          proof (cases "is_tautology C' \<or> subsume (map fst P @ map fst Q) C'")
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
                      wrp.tautology_deletion[of A "mset C'" "mset (map (apfst mset) N')" i
                        "mset (map (apfst mset) P)" "mset (map (apfst mset) Q)" n]])
                  (use neg_a pos_a in simp_all)
            next
              case False
              then have "subsume (map fst P @ map fst Q) C'"
                using taut_or_subs by blast
              then obtain D :: "'a lclause" where
                d_in: "D \<in> set (map fst P @ map fst Q)" and
                subs: "subsumes (mset D) (mset C')"
                unfolding subsume_def by blast
              show ?thesis
                by (rule arg_cong2[THEN iffD1, of _ _ _ _ "op \<leadsto>\<^sub>w", OF _ _
                      wrp.forward_subsumption[of "mset D" "mset (map (apfst mset) P)"
                        "mset (map (apfst mset) Q)" "mset C'" "mset (map (apfst mset) N')" i n]],
                    use d_in subs in \<open>auto simp: subsume_def\<close>)
            qed
            then show ?thesis
              unfolding step st n_cons ci using red_C by (rule rtranclp_into_tranclp1[rotated])
          next
            case not_taut_or_subs: False
            note step = step[simplified not_taut_or_subs, simplified]

            obtain back_to_P Q' :: "'a dclause list" where
              red_Q: "(back_to_P, Q') = reduce_all2 [C'] Q"
              by (metis prod.exhaust)
            note step = step[unfolded red_Q[symmetric], simplified]

            define P' :: "('a literal list \<times> nat) list" where
              "P' = reduce_all [C'] (back_to_P @ P)"
            define Q'' :: "('a literal list \<times> nat) list" where
              "Q'' = filter (Not \<circ> strictly_subsume [C'] \<circ> fst) Q'"
            define P'' :: "('a literal list \<times> nat) list" where
              "P'' = filter (Not \<circ> strictly_subsume [C'] \<circ> fst) P'"
            note step = step[unfolded P'_def[symmetric] Q''_def[symmetric] P''_def[symmetric],
                simplified]

            note red_C
            also have "wstate_of_dstate ((C', i) # N', P, Q, n)
              \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((C', i) # N', back_to_P @ P, Q', n)"
              by (rule reduce_clauses_in_Q[of C' _ _ "[]" Q, folded red_Q,
                    unfolded append_Nil prod.sel])
                simp
            also have "\<dots> \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((C', i) # N', P', Q', n)"
              unfolding P'_def by (rule reduce_clauses_in_P[of _ _ "[]", unfolded append_Nil]) simp
            also have "\<dots> \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((C', i) # N', P', Q'', n)"
              unfolding Q''_def
              by (rule remove_strictly_subsumed_clauses_in_Q[of _ _ _ "[]", unfolded append_Nil])
                simp
            also have "\<dots> \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((C', i) # N', P'', Q'', n)"
              unfolding P''_def
              by (rule remove_strictly_subsumed_clauses_in_P[of _ _ "[]", unfolded append_Nil]) simp
            also note proc_C[THEN tranclp.r_into_trancl[of "op \<leadsto>\<^sub>w"]]
            finally show ?thesis
              unfolding step st n_cons ci .
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

    obtain N' P' Q' :: "'a dclause list" and n' k :: nat where
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

lemma finite_ssgSts0: "finite (wrp.clss_of_wstate (lhd ssgSts))"
  unfolding lhd_ssgSts by (subst derivation_from.code) (simp add: clss_of_state_def)

lemma empty_ssgP0: "wrp.P_of_wstate (lhd ssgSts) = {}"
  unfolding lhd_ssgSts by (subst derivation_from.code) simp

lemma empty_ssgQ0: "wrp.Q_of_wstate (lhd ssgSts) = {}"
  unfolding lhd_ssgSts by (subst derivation_from.code) simp

lemmas ssgSts_thms = deriv_ssgSts_weighted_RP finite_ssgSts0 empty_ssgP0 empty_ssgQ0

lemma "clss_of_state (wrp.Liminf_wstate ssgSts) \<subseteq> clss_of_state (wrp.Liminf_wstate gSts)"
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
  "S_ssgQ \<equiv> wrp.S_gQ ssgSts"

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
  obtain N' P' Q' :: "'a dclause list" and n' k :: nat where
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

  have fin_gr_fgsts: "lfinite (lmap wrp.grounding_of_wstate ssgSts)"
    by (rule lfinite_lmap[THEN iffD2, OF lfinite_ssgSts])

  have lim_last: "Liminf_llist (lmap wrp.grounding_of_wstate ssgSts) =
    wrp.grounding_of_wstate (llast ssgSts)"
    unfolding lfinite_Liminf_llist[OF fin_gr_fgsts]
      llast_lmap[OF lfinite_ssgSts not_lnull_ssgSts]
    using not_lnull_ssgSts by simp

  have gr_st0: "wrp.grounding_of_wstate (wstate_of_dstate St0) = grounded_N0"
    by (simp add: clss_of_state_def comp_def)

  have "?saturated \<and> ?model"
  proof (cases "[] \<in> set R")
    case True
    then have emp_in: "{#} \<in> grounded_R"
      unfolding grounding_of_clss_def grounding_of_cls_def by (auto intro: ex_ground_subst)

    have "grounded_R \<subseteq> wrp.grounding_of_wstate (llast ssgSts)"
      unfolding r llast_ssgSts
      by (simp add: last_sts llast_lmap[OF lfinite_Sts] clss_of_state_def grounding_of_clss_def)
    then have gr_last_st: "grounded_R \<subseteq> wrp.grounding_of_wstate (wstate_of_dstate (llast Sts))"
      by (simp add: lfinite_Sts llast_lmap llast_ssgSts)

    have gr_r_fls: "\<not> I \<Turnstile>s grounded_R"
      using emp_in unfolding true_clss_def by force
    then have gr_last_fls: "\<not> I \<Turnstile>s wrp.grounding_of_wstate (wstate_of_dstate (llast Sts))"
      using gr_last_st unfolding true_clss_def by auto

    have ?saturated
      unfolding wrp.ord_\<Gamma>_saturated_upto_def[OF ssgSts_thms]
        wrp.ord_\<Gamma>_contradiction_Rf[OF ssgSts_thms emp_in] inference_system.inferences_from_def
      by auto
    moreover have ?model
      unfolding gr_r_fls[THEN eq_False[THEN iffD2]]
      by (rule rtranclp_imp_eq_image[of "op \<leadsto>\<^sub>w" "\<lambda>St. I \<Turnstile>s wrp.grounding_of_wstate St", OF _ wrp,
            unfolded gr_st0 gr_last_fls[THEN eq_False[THEN iffD2]]])
        (use wrp.weighted_RP_model[OF ssgSts_thms] in blast)
    ultimately show ?thesis
      by blast
  next
    case False
    then have gr_last: "wrp.grounding_of_wstate (llast ssgSts) = grounded_R"
      using final unfolding r llast_ssgSts
      by (simp add: last_sts llast_lmap[OF lfinite_Sts] clss_of_state_def comp_def
          is_final_dstate.simps)
    then have gr_last_st: "wrp.grounding_of_wstate (wstate_of_dstate (llast Sts)) = grounded_R"
      by (simp add: lfinite_Sts llast_lmap llast_ssgSts)

    have ?saturated
      using wrp.weighted_RP_saturated[OF ssgSts_thms, unfolded gr_last lim_last] by auto
    moreover have ?model
      by (rule rtranclp_imp_eq_image[of "op \<leadsto>\<^sub>w" "\<lambda>St. I \<Turnstile>s wrp.grounding_of_wstate St", OF _ wrp,
            unfolded gr_st0 gr_last_st])
        (use wrp.weighted_RP_model[OF ssgSts_thms] in blast)
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
    unfolding wrp.ord_\<Gamma>_saturated_upto_complete[OF ssgSts_thms deterministic_RP_saturated] .
qed

end

context
  assumes drp_none: "deterministic_RP St0 = None"
begin

theorem deterministic_RP_complete: "satisfiable grounded_N0"
proof (rule ccontr)
  assume unsat: "\<not> satisfiable grounded_N0"

  have unsat_gSts0: "\<not> satisfiable (wrp.grounding_of_wstate (lhd gSts))"
    using unsat by (subst derivation_from.code) (simp add: clss_of_state_def comp_def)

  have bot_in_ss: "{#} \<in> Q_of_state (wrp.Liminf_wstate ssgSts)"
    by (rule wrp.weighted_RP_complete[OF ssgSts_thms unsat_gSts0[folded lhd_ssgSts]])
  have bot_in_lim: "{#} \<in> Q_of_state (wrp.Liminf_wstate gSts)"
  proof (cases "lfinite Sts")
    case fin: True
    have "wrp.Liminf_wstate ssgSts = wrp.Liminf_wstate gSts"
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
  then obtain k :: nat where
    k_lt: "enat k < llength Sts" and
    emp_in: "{#} \<in> wrp.Q_of_wstate (lnth gSts k)"
    unfolding Liminf_state_def Liminf_llist_def by auto
  have emp_in: "{#} \<in> Q_of_state (state_of_dstate ((deterministic_RP_step ^^ k) St0))"
  proof -
    have "enat k < llength Sts' \<Longrightarrow> Sts' = derivation_from St0' \<Longrightarrow>
      {#} \<in> wrp.Q_of_wstate (lnth (lmap wstate_of_dstate Sts') k) \<Longrightarrow>
      {#} \<in> Q_of_state (state_of_dstate ((deterministic_RP_step ^^ k) St0'))" for St0' Sts' k
    proof (induction k arbitrary: St0' Sts')
      case 0
      then show ?case
        by (subst (asm) derivation_from.code, cases St0', auto simp: comp_def)
    next
      case (Suc k)
      note ih = this(1) and sk_lt = this(2) and sts' = this(3) and emp_in_sk = this(4)

      have k_lt: "enat k < llength (ltl Sts')"
        using sk_lt by (cases Sts') (auto simp: Suc_ile_eq)
      moreover have "ltl Sts' = derivation_from (deterministic_RP_step St0')"
        using sts' k_lt by (cases Sts') auto
      moreover have "{#} \<in> wrp.Q_of_wstate (lnth (lmap wstate_of_dstate (ltl Sts')) k)"
        using emp_in_sk k_lt by (cases Sts') auto
      ultimately show ?case
        using ih[of "ltl Sts'" "deterministic_RP_step St0'"] by (simp add: funpow_swap1)
    qed
    then show ?thesis
      using k_lt emp_in by blast
  qed
  have "deterministic_RP St0 \<noteq> None"
    by (rule is_final_dstate_funpow_imp_deterministic_RP_neq_None[of k],
        cases "(deterministic_RP_step ^^ k) St0",
        use emp_in in \<open>force simp: is_final_dstate.simps comp_def image_def\<close>)
  then show False
    using drp_none ..
qed

end

end

end

end
