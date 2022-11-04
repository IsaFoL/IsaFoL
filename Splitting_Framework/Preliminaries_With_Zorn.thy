(* Title:        Preliminaries of the Splitting Framework
 * Author:       Sophie Tourret <stourret at mpi-inf.mpg.de>, 2020-2022
 *               Florent Krasnopol <florent.krasnopol at ens-paris-saclay.fr>, 2022 *)

theory Preliminaries_With_Zorn
  imports Saturation_Framework.Calculus
    Propositional_Proof_Systems.Compactness
    "HOL-Library.Library"
    "HOL-Library.Product_Lexorder"
  (* Finite_Set *)
begin

no_notation Sema.formula_semantics (infix "\<Turnstile>" 51)

  (*useful tools for the following proofs*)

lemma pow_suc: \<open>(f^^(Suc k)) x = (f^^k) (f x)\<close>
  by (induction k) auto

lemma finite_because_singleton: \<open>(\<forall>C1 \<in> S. \<forall>C2 \<in> S. C1 = C2) \<longrightarrow> finite S\<close> for S
  by (metis finite.simps is_singletonI' is_singleton_the_elem)

lemma finite_union_of_finite_is_finite: \<open>finite E \<Longrightarrow> (\<forall>D \<in> E. finite({f C |C. P C \<and> g C = D})) \<Longrightarrow>
                                  finite({f C |C. P C \<and> g C \<in> E})\<close>
proof -
  assume finite_E: \<open>finite E\<close> and
         all_finite: \<open>\<forall>D \<in> E. finite({f C |C. P C \<and> g C = D})\<close>
  have \<open>finite (\<Union>{{f C |C. P C \<and> g C = D} |D. D\<in>E})\<close>
    using finite_E all_finite finite_UN_I
    by (simp add: setcompr_eq_image)
  moreover have \<open>{f C |C. P C \<and> g C \<in> E} \<subseteq> \<Union>{{f C |C. P C \<and> g C = D} |D. D\<in>E}\<close>
    by blast
  ultimately show ?thesis by (meson finite_subset)
qed

  (* formalizing negated formulas uncovered a mistake in the corresponding paper-definition
  (sect. 2.1) *)

(* old def of sign datatype, that causes *a lot* of trouble *)
  (* datatype 'a neg = Pos "'a" | Neg "'a neg" *)
(* ("\<sim>_" 55) (*| Pos (nval_of: "'a neg") *) term "\<sim>F" *)

datatype 'a sign = Pos "'a" | Neg "'a"

thm countable_classI

instance sign :: (countable) countable
  by (rule countable_classI [of "(\<lambda>x. case x of Pos x \<Rightarrow> to_nat (True, to_nat x)
                                                  | Neg x \<Rightarrow> to_nat (False, to_nat x))"])
     (smt (verit, best) Pair_inject from_nat_to_nat sign.exhaust sign.simps(5) sign.simps(6))

term \<open>less_eq (a::nat) b\<close>

(*
lift_definition less_eq_sign :: "'a::{countable,linorder} sign \<Rightarrow> 'a sign \<Rightarrow> bool" is
  \<open>a \<le> b = less_eq (to_nat (a::('a::{countable, linorder}) sign)) (to_nat b)\<close>
*)

find_theorems "_ \<Longrightarrow> OFCLASS(_,linorder_class)"

(*
instance sign :: (linorder) linorder
  apply (rule Orderings.class.Orderings.linorder.of_class.intro)
  unfolding class.linorder_def class.order_def class.preorder_def class.order_axioms_def
    class.linorder_axioms_def
  apply auto
  sorry  
*)

fun neg :: \<open>'a sign \<Rightarrow> 'a sign\<close> where
  \<open>neg (Pos C) = Neg C\<close> |
  \<open>neg (Neg C) = Pos C\<close>

fun to_V :: "'a sign \<Rightarrow> 'a" where
  "to_V (Pos C) = C" |
  "to_V (Neg C) = C"

fun is_Pos :: "'a sign \<Rightarrow> bool" where
  "is_Pos (Pos C) = True" |
  "is_Pos (Neg C) = False"

lemma is_Pos_to_V: \<open>is_Pos C \<Longrightarrow> C = Pos (to_V C)\<close>
  by (metis is_Pos.simps(2) to_V.elims)

lemma is_Neg_to_V: \<open>\<not> is_Pos C \<Longrightarrow> C = Neg (to_V C)\<close>
  by (metis is_Pos.simps(1) to_V.elims)

lemma pos_union_singleton: \<open>{D. Pos D \<in> N \<union> {Pos X}} = {D. Pos D \<in> N} \<union> {X}\<close>
  by blast

lemma tov_set[simp]: \<open>{to_V C |C. to_V C \<in> A} = A\<close>
  by (smt (verit, del_insts) mem_Collect_eq subsetI subset_antisym to_V.simps(1))

lemma pos_neg_union: \<open>{P C |C. Q C \<and> is_Pos C} \<union> {P C |C. Q C \<and> \<not> is_Pos C} = {P C |C. Q C}\<close>
  by blast
 
locale consequence_relation =
  fixes
    bot :: "'f" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50)
  assumes
    bot_entails_empty: "{bot} \<Turnstile> {}" and
    entails_reflexive: "{C} \<Turnstile> {C}" and
    entails_subsets: "M' \<subseteq> M \<Longrightarrow> N' \<subseteq> N \<Longrightarrow> M' \<Turnstile> N' \<Longrightarrow> M \<Turnstile> N" and
    entails_cut: "M \<Turnstile> N \<union> {C} \<Longrightarrow> M' \<union> {C} \<Turnstile> N' \<Longrightarrow> M \<union> M'\<Turnstile> N \<union> N'" and
    entails_compactness: "M \<Turnstile> N \<Longrightarrow> \<exists> M' N'. (M' \<subseteq> M \<and> N' \<subseteq> N \<and> finite M' \<and> finite N' \<and> M' \<Turnstile> N')"
    (*entails_supsets: "(\<forall>M' N'. (M' \<supseteq> M \<and> N' \<supseteq> N \<and> M' \<union> N' = UNIV) \<longrightarrow> M' \<Turnstile> N') \<Longrightarrow> M \<Turnstile> N"*)
    (* the version of D4 below was relaxed to fix lemma 6, which was found broken due to the forma *)
    (* entails_each: "M \<Turnstile> P \<Longrightarrow> \<forall>C\<in>M. N \<Turnstile> Q \<union> {C} \<Longrightarrow> \<forall>D\<in>P. N \<union> {D} \<Turnstile> Q \<Longrightarrow> N \<Turnstile> Q" *)
    (* this was an earlier version of entails_each: "M \<Turnstile> N \<Longrightarrow> (\<forall>D\<in>N. M \<union> {D} \<Turnstile> P) \<Longrightarrow> M \<Turnstile> P"
    it was detected to be unsufficient thanks to the forma*)
begin


definition order_double_subsets :: "('f set * 'f set) \<Rightarrow> ('f set * 'f set) \<Rightarrow> bool"
      (infix "\<preceq>\<^sub>s" 50) where
      \<open>(\<preceq>\<^sub>s) \<equiv> \<lambda>C1 C2. fst C1 \<subseteq> fst C2 \<and> snd C1 \<subseteq> snd C2\<close>
definition order_double_subsets_strict :: "('f set * 'f set) \<Rightarrow> ('f set * 'f set) \<Rightarrow> bool"
      (infix "\<prec>\<^sub>s" 50) where
      \<open>(\<prec>\<^sub>s) \<equiv> \<lambda>C1 C2. C1 \<preceq>\<^sub>s C2 \<and> C1 \<noteq> C2\<close>

lemma trivial_induction_order : \<open>C1 \<subseteq> B \<and> C2 \<subseteq> B' \<longrightarrow> (C1,C2) \<preceq>\<^sub>s (B,B')\<close>
      unfolding order_double_subsets_def
      by simp

lemma zorn_relation_trans : \<open>\<forall>C1 C2 C3. (C1 \<preceq>\<^sub>s C2) \<longrightarrow> (C2 \<preceq>\<^sub>s C3) \<longrightarrow> (C1 \<preceq>\<^sub>s C3)\<close>
    proof -
      have \<open>\<forall>C1 C2 C3. fst C1 \<subseteq> fst C2 \<longrightarrow> fst C2 \<subseteq> fst C3 \<longrightarrow> fst C1 \<subseteq> fst C3\<close>
        by blast
      then  have \<open>\<forall>C1 C2 C3. snd C1 \<subseteq> snd C2 \<longrightarrow> snd C2 \<subseteq> snd C3 \<longrightarrow> snd C1 \<subseteq> snd C3\<close>
        by blast
      then show ?thesis
        unfolding order_double_subsets_def
        by auto
    qed

lemma zorn_strict_relation_trans :
  \<open>\<forall>(C1::'f set \<times> 'f set) C2 C3. (C1 \<prec>\<^sub>s C2) \<longrightarrow> (C2 \<prec>\<^sub>s C3) \<longrightarrow> (C1 \<prec>\<^sub>s C3)\<close>
  by (metis order_double_subsets_def order_double_subsets_strict_def prod.expand subset_antisym
        zorn_relation_trans)

lemma zorn_relation_antisym :  \<open>\<forall>C1 C2. (C1 \<preceq>\<^sub>s C2) \<longrightarrow> (C2 \<preceq>\<^sub>s C1) \<longrightarrow> (C1 = C2)\<close>
    proof -
      have \<open>\<forall>C1 C2. (fst C1 \<subseteq> fst C2) \<longrightarrow> (fst C2 \<subseteq> fst C1) \<longrightarrow> (fst C1 = fst C2)\<close>
        by force
      then have \<open>\<forall>C1 C2. (snd C1 \<subseteq> snd C2) \<longrightarrow> (snd C2 \<subseteq> snd C1) \<longrightarrow> (snd C1 = snd C2)\<close>
        by force
      then show ?thesis
        unfolding order_double_subsets_def
        using dual_order.eq_iff
        by auto
    qed

lemma entails_supsets : "(\<forall>M' N'. (M' \<supseteq> M \<and> N' \<supseteq> N \<and> M' \<union> N' = UNIV) \<longrightarrow> M' \<Turnstile> N') \<Longrightarrow> M \<Turnstile> N"
proof (rule ccontr)
  assume
    not_M_entails_N : \<open>\<not>M \<Turnstile> N\<close> and
    hyp_entails_sup : \<open>(\<forall>M' N'. (M' \<supseteq> M \<and> N' \<supseteq> N \<and> M' \<union> N' = UNIV) \<longrightarrow> M' \<Turnstile> N')\<close>
  have contrapos_hyp_entails_sup: \<open>\<exists>M' N'. (M' \<supseteq> M \<and> N' \<supseteq> N \<and> M' \<union> N' = UNIV) \<and> \<not>M' \<Turnstile> N'\<close>
  proof -
    define A  :: "('f set * 'f set) set" where \<open>A = {(M',N'). M \<subseteq> M' \<and> N \<subseteq> N' \<and> \<not>M' \<Turnstile> N'}\<close>
    define zorn_relation :: "(('f set * 'f set) \<times> ('f set * 'f set)) set" where
      \<open>zorn_relation = {(C1,C2) \<in> A \<times> A. C1\<preceq>\<^sub>sC2}\<close>
    define max_chain :: "('f set * 'f set) set \<Rightarrow> 'f set * 'f set" where
      \<open>max_chain = (\<lambda>C. if C = {} then (M,N)
                            else (\<Union>{C1. \<exists>C2. (C1,C2) \<in> C},\<Union>{C2. \<exists>C1. (C1,C2) \<in> C}))\<close>

(*minor properties on zorn_relation and chains*)
    have relation_in_A : \<open>\<And>C. C \<in> Chains zorn_relation \<Longrightarrow> \<forall> C1 \<in> C. C1 \<in> A\<close>
      using in_ChainsD zorn_relation_def 
      by (metis (no_types, lifting) mem_Collect_eq mem_Sigma_iff old.prod.case)
    have M_N_in_A : \<open>(M,N) \<in> A\<close>
      using not_M_entails_N A_def by simp
    then have not_empty_A :  \<open>A\<noteq>{}\<close>
      by force 

(*we show that zorn_relation is a partial order*)
    have trivial_replacement_order [simp] : \<open>\<forall>C1 C2. (C1,C2) \<in> zorn_relation  \<longrightarrow> (C1 \<preceq>\<^sub>s C2)\<close>
      unfolding zorn_relation_def by force
    moreover have zorn_relation_refl : \<open>\<forall>C\<in>A. C \<preceq>\<^sub>s C\<close>
    proof -
      have \<open>\<forall>C\<in>A. fst C \<subseteq> fst C \<and> snd C \<subseteq> snd C\<close>
        by blast
      then show ?thesis 
        unfolding order_double_subsets_def
        by simp
    qed
    moreover have refl_on_zorn_relation : "refl_on A zorn_relation"
      using zorn_relation_refl
      by (smt (verit, ccfv_SIG) case_prod_conv mem_Collect_eq mem_Sigma_iff refl_onI 
          subrelI zorn_relation_def)
    moreover have zorn_relation_field_is_A :  "Field zorn_relation = A"
    proof -
      have \<open>\<forall> C0 \<in> A. (M,N) \<preceq>\<^sub>s C0\<close>
        unfolding order_double_subsets_def
        using A_def by simp
      then have \<open>\<forall> C0 \<in> A. ((M,N),C0) \<in> zorn_relation\<close>
        unfolding zorn_relation_def
        using M_N_in_A by simp
      then have "A \<subseteq> Range zorn_relation"
        unfolding Range_def by fast
      moreover have \<open>\<forall>C0. C0 \<in> (Range zorn_relation) \<longrightarrow> C0 \<in> A\<close>
        by (meson Range_iff refl_on_zorn_relation refl_onD2)
      moreover have \<open>\<forall>C0. C0 \<in> (Domain zorn_relation) \<longrightarrow> C0 \<in> A\<close>
        by (metis Domain.cases refl_on_zorn_relation refl_on_domain)
      ultimately show ?thesis
        by (metis Field_def Un_absorb1 subrelI subset_antisym)
    qed
    ultimately have zorn_hypothesis_po: "Partial_order zorn_relation"
    proof -
      have antisym_zorn_relation : "antisym zorn_relation"
      proof -
        have \<open>\<forall>C1 C2. (C1,C2) \<in> zorn_relation \<and> (C2,C1) \<in> zorn_relation \<longrightarrow> (C1 \<preceq>\<^sub>s C2) \<and> (C2 \<preceq>\<^sub>s C1)\<close>
          by force
        then show ?thesis using zorn_relation_antisym
          by (meson antisymI)
      qed

      moreover have "trans zorn_relation"
      proof -
        have \<open>\<forall>C1 C2 C3. (C1,C2) \<in> zorn_relation
               \<longrightarrow> (C2,C3) \<in> zorn_relation \<longrightarrow> (C1 \<preceq>\<^sub>s C2) \<longrightarrow> (C2 \<preceq>\<^sub>s C3)\<close>
          unfolding zorn_relation_def by blast
        then  have \<open>\<forall>C1\<in>A. \<forall>C2\<in>A. (C1 \<preceq>\<^sub>s C2) \<longrightarrow> (C1,C2) \<in> zorn_relation\<close>
          unfolding zorn_relation_def by blast
        then show ?thesis using zorn_relation_trans
          by (metis (no_types, opaque_lifting) FieldI1 FieldI2 transI 
              trivial_replacement_order zorn_relation_field_is_A zorn_relation_trans)
      qed

      ultimately have "preorder_on A zorn_relation"
        unfolding preorder_on_def refl_on_zorn_relation
        using refl_on_zorn_relation by simp
      then have "partial_order_on A zorn_relation"
        unfolding partial_order_on_def
        using antisym_zorn_relation by simp
      moreover have zorn_relation_field :  "Field zorn_relation = A"
      proof -
        have \<open>\<forall> C0 \<in> A. (M,N) \<preceq>\<^sub>s C0\<close>
          unfolding order_double_subsets_def
          using A_def by simp
        then have \<open>\<forall> C0 \<in> A. ((M,N),C0) \<in> zorn_relation\<close>
          unfolding zorn_relation_def
          using M_N_in_A by simp
        then have "A \<subseteq> Range zorn_relation"
          unfolding Range_def by fast
        moreover have \<open>\<forall>C0. C0 \<in> (Range zorn_relation) \<longrightarrow> C0 \<in> A\<close>
          by (meson Range_iff refl_on_zorn_relation refl_onD2)
        moreover have \<open>\<forall>C0. C0 \<in> (Domain zorn_relation) \<longrightarrow> C0 \<in> A\<close>
          by (metis Domain.cases refl_on_zorn_relation refl_on_domain)
        ultimately show ?thesis
          by (metis Field_def Un_absorb1 subrelI subset_antisym)
      qed

      show ?thesis using zorn_relation_field calculation by simp
    qed

(*we show that max_chain C is an upper bound of C for all chain C*)
    have max_chain_is_a_max : \<open>\<And>C. C \<in> Chains zorn_relation \<Longrightarrow> \<forall>C1\<in>C. (C1 \<preceq>\<^sub>s max_chain C)\<close>
    proof -
      fix C
      assume C_is_a_chain : \<open>C \<in> Chains zorn_relation\<close>
      consider (a) "C = {}" | (b) "C \<noteq> {}"
        by auto
      then show \<open>\<forall> C1 \<in> C. C1 \<preceq>\<^sub>s max_chain C\<close>
      proof cases
        case a
        show ?thesis  by (simp add: a)
      next
        case b
        have \<open>C \<subseteq> A\<close>
          using C_is_a_chain relation_in_A by blast
        then have \<open>\<forall> C1 \<in> C. \<exists> (C2,C3) \<in> C. C1 = (C2,C3)\<close>
          by blast
        moreover have  \<open>\<forall> (C1,C2) \<in> C. C1 \<subseteq> \<Union>{C3. \<exists> C4. (C3,C4) \<in> C}\<close>
          by blast
        moreover have \<open>\<forall> (C1,C2) \<in> C. C2 \<subseteq> \<Union>{C4. \<exists> C3. (C3,C4) \<in> C}\<close>
          by blast
        moreover have \<open>\<forall> (C1,C2) \<in> C. 
                    ((C1 \<subseteq> \<Union>{C3. \<exists> C4. (C3,C4) \<in> C} \<and> C2 \<subseteq> \<Union>{C4. \<exists> C3. (C3,C4) \<in> C}) \<longrightarrow>
                      (C1,C2) \<preceq>\<^sub>s (\<Union>{C3. \<exists> C4. (C3,C4) \<in> C}, \<Union>{C4. \<exists> C3. (C3,C4) \<in> C}))\<close>
          unfolding order_double_subsets_def
          using trivial_induction_order
          by simp
        ultimately have \<open>\<forall> (C1,C2) \<in> C. 
                        (C1,C2) \<preceq>\<^sub>s (\<Union>{C3. \<exists> C4. (C3,C4) \<in> C},\<Union>{C4. \<exists> C3. (C3,C4) \<in> C})\<close>
          by fastforce
        then have \<open>\<forall> (C1,C2) \<in> C. (C1,C2) \<preceq>\<^sub>s max_chain C\<close>
          unfolding max_chain_def
          by simp
        then show \<open>\<forall> C1 \<in> C. C1 \<preceq>\<^sub>s max_chain C\<close>
          by fast
      qed
    qed

(*we show that max_chain C is in A*)
    have M_N_less_than_max_chain : \<open>\<And>C. C \<in> Chains zorn_relation \<Longrightarrow> (M,N) \<preceq>\<^sub>s max_chain C\<close>
    proof -
      fix C
      assume C_chain : \<open>C \<in> Chains zorn_relation\<close>
      consider (a) "C = {}" | (b) "C \<noteq> {}"
        by blast
      then show \<open>(M,N) \<preceq>\<^sub>s max_chain C\<close>
      proof cases
        case a
        assume "C = {}"
        then have \<open>max_chain C = (M,N)\<close>
          unfolding max_chain_def 
          by simp
        then show \<open>(M,N) \<preceq>\<^sub>s max_chain C\<close>
          using M_N_in_A zorn_relation_refl
          by simp
      next
        case b
        assume C_not_empty : "C \<noteq> {}"
        have M_minor_first : \<open>\<forall> C1 \<in> C. M \<subseteq> fst C1\<close>
          using A_def C_chain relation_in_A by fastforce
        have N_minor_second :  \<open>\<forall> C1 \<in> C. N \<subseteq> snd C1\<close>
          using A_def C_chain relation_in_A by fastforce
        moreover have \<open>(\<forall> C1 \<in> C. (fst C1 \<subseteq> fst (max_chain C)) \<and> snd C1 \<subseteq> snd (max_chain C))\<close>
          using order_double_subsets_def C_chain max_chain_is_a_max
          by presburger
        moreover have \<open>(\<exists>C1 \<in> C. (M \<subseteq> fst C1 \<and> N \<subseteq> snd C1)
                               \<longrightarrow> fst C1 \<subseteq> fst (max_chain C) \<and> snd C1 \<subseteq> snd (max_chain C))
                       \<longrightarrow> M \<subseteq> fst (max_chain C) \<and> N \<subseteq> snd (max_chain C)\<close>
          using M_minor_first N_minor_second
          by blast
        ultimately have  \<open>M \<subseteq> fst (max_chain C) \<and> N \<subseteq> snd (max_chain C)\<close>
          by (meson order_double_subsets_def C_chain C_not_empty ex_in_conv max_chain_is_a_max)
        then show  \<open>(M,N) \<preceq>\<^sub>s max_chain C\<close>
          unfolding order_double_subsets_def
          by simp
      qed
    qed
    moreover have left_U_not_entails_right_U:
      \<open>\<And>C. C \<in> Chains zorn_relation \<Longrightarrow> \<not> fst (max_chain C)\<Turnstile> snd (max_chain C)\<close>
    proof -
      fix C
      assume C_chain :\<open>C \<in> Chains zorn_relation\<close>
      consider (a) "C = {}" | (b) "C \<noteq> {}"
        by fast
      then show \<open>\<not> fst (max_chain C)\<Turnstile> snd (max_chain C)\<close>
      proof cases
        case a
        then show ?thesis using not_M_entails_N
          unfolding max_chain_def
          by simp
      next
        case b
        assume C_not_empty :\<open>C \<noteq> {}\<close>
        show ?thesis
        proof (rule ccontr)
          assume \<open>\<not>\<not>fst (max_chain C) \<Turnstile> snd (max_chain C)\<close>
          then have abs_fst_entails_snd : \<open>fst (max_chain C) \<Turnstile> snd (max_chain C)\<close>
            by auto
          then obtain M' N' where 
            abs_max_chain_compactness : \<open>M' \<subseteq> fst (max_chain C) 
                                         \<and> N' \<subseteq> snd (max_chain C) 
                                         \<and> finite M'
                                         \<and> finite N'
                                         \<and> M' \<Turnstile> N'\<close>
            using entails_compactness  by fastforce
          then have not_empty_M'_or_N' : \<open>(M' \<noteq> {}) \<or> (N' \<noteq> {})\<close>
            by (meson empty_subsetI entails_subsets not_M_entails_N)
          then have finite_M'_subset : \<open>(finite M') \<and> M' \<subseteq> \<Union>{C1. \<exists>C2. (C1,C2) \<in> C}\<close>
            using C_not_empty abs_max_chain_compactness max_chain_def
            by simp
          then have M'_in_great_union : \<open>M' \<subseteq> \<Union>{C1. \<exists>C2. (C1,C2) \<in> C \<and> C1 \<inter> M' \<noteq> {}}\<close>
            by blast
          then have M'_in_finite_union : 
            \<open>\<exists>P \<subseteq> {C1. \<exists>C2. (C1,C2) \<in> C \<and> C1 \<inter> M' \<noteq> {}}. finite P \<and> M' \<subseteq> \<Union>P\<close>
            by (meson finite_M'_subset finite_subset_Union)
          moreover have finite_N'_subset : \<open>(finite N') \<and> N' \<subseteq> \<Union>{C2. \<exists>C1. (C1,C2) \<in> C}\<close>
            using C_not_empty abs_max_chain_compactness
            using max_chain_def
            by simp
          then have N'_in_great_union : \<open>N' \<subseteq> \<Union>{C2. \<exists>C1. (C1,C2) \<in> C \<and> C2 \<inter> N' \<noteq> {}}\<close>
            by blast
          then have N'_in_finite_union : 
            \<open>\<exists>Q \<subseteq> {C2. \<exists>C1. (C1,C2) \<in> C \<and> C2 \<inter> N' \<noteq> {}}. finite Q \<and> N' \<subseteq> \<Union>Q\<close>
            by (meson finite_N'_subset finite_subset_Union)

          ultimately obtain P Q where 
            P_subset : \<open>P \<subseteq> {C1. \<exists>C2. (C1,C2) \<in> C \<and> C1 \<inter> M' \<noteq> {}}\<close> and 
            finite_P: \<open>finite P\<close> and 
            P_supset : \<open>M' \<subseteq> \<Union>P\<close> and 
            Q_subset : \<open>Q \<subseteq> {C2. \<exists>C1. (C1,C2) \<in> C \<and> C2 \<inter> N' \<noteq> {}}\<close> 
            and finite_Q : \<open>finite Q\<close> and Q_supset : \<open>N' \<subseteq> \<Union>Q\<close>      
            by auto
          have not_empty_P_or_Q : \<open>P \<noteq> {} \<or> Q \<noteq> {}\<close>
            using not_empty_M'_or_N' P_supset Q_supset by blast
          have P_linked_C : \<open>\<forall>C1\<in>P. \<exists>C2. (C1,C2)\<in>C\<close>
            using P_subset by auto
          then have Q_linked_C : \<open>\<forall>C2\<in>Q. \<exists>C1. (C1,C2)\<in>C\<close>
            using Q_subset by auto
          then have \<open>\<exists>\<P> \<subseteq> C. \<P> = {(C1,C2). (C1,C2) \<in> C \<and> C1 \<in> P}\<close>
            by fastforce

          then obtain \<P> where 
            \<P>_def: \<open>\<P> = {(C1,C2). (C1,C2) \<in> C \<and> C1 \<in> P}\<close>
            by auto
          then have \<P>_in_C : \<open>\<P> \<subseteq> C\<close>
            by auto
          have P_linked_\<P> : \<open>\<forall>C1\<in>P. \<exists>C2. (C1,C2)\<in>\<P>\<close>
            using P_linked_C \<P>_def
            by simp

          define f where 
            \<open>f = (\<lambda>C1. if (\<exists>C2. (C1,C2)\<in>\<P>) then (SOME C2. (C1,C2) \<in> \<P>) else {})\<close>
          have \<open>\<forall>(C1,C2)\<in>\<P>. C1\<in>P\<close>
            using \<P>_def by blast
          have f_stability_in_\<P> : \<open>\<And> C1 C2. (C1,C2)\<in>\<P> \<Longrightarrow> (C1, f C1)\<in>\<P>\<close>
          proof -
            fix C1 C2
            show  \<open>(C1,C2)\<in>\<P> \<Longrightarrow> (C1, f C1)\<in>\<P>\<close>
            proof -
              assume C1_C2_in_\<P> : \<open>(C1,C2)\<in>\<P>\<close>
              then have \<open>\<exists>C3. (C1,C3)\<in>\<P>\<close>
                by blast
              then have \<open>(C1, f C1) = (C1, SOME C3. (C1,C3) \<in> \<P>)\<close>
                unfolding f_def by simp
              then have \<open>(C1, f C1)\<in>\<P>\<close>
                by (metis C1_C2_in_\<P> someI_ex)
              then show  \<open>(C1,C2)\<in>\<P> \<Longrightarrow> (C1, f C1)\<in>\<P>\<close> by blast
            qed
          qed

          define \<P>' where 
            \<open>\<P>' = {(C1, f C1)|C1. \<exists>C2. (C1,C2)\<in>\<P>}\<close>
          then have injectivity_\<P>' : \<open>\<forall>C1 C2 C2'.(((C1, C2) \<in> \<P>' \<and> (C1, C2') \<in> \<P>') \<longrightarrow> C2 = C2')\<close>
            by auto
          have \<P>'_in_\<P> : \<open>\<P>' \<subseteq> \<P>\<close>
            unfolding \<P>'_def
            using f_stability_in_\<P>
            by blast
          then have \<P>'_in_C : \<open>\<P>' \<subseteq> C\<close>
            using \<P>_in_C
            by blast
          have \<P>'_less_than_P : \<open>\<forall>C0 \<in> \<P>'. fst C0\<in>P\<close>
            unfolding \<P>'_def \<P>_def by fastforce
          have P_less_than_\<P> : \<open>\<forall>C1 \<in> P. \<exists>C2. (C1,C2)\<in>\<P>\<close>
            unfolding \<P>_def
            using P_linked_C by simp
          then have P_less_than_\<P>_reformulated : \<open>\<forall>C1 \<in> P. \<exists>C0\<in>\<P>'. (fst C0) = C1\<close>
            unfolding \<P>'_def
            by simp
          then have union_P_in_union_fst_\<P>' : \<open>\<Union>P \<subseteq> \<Union>{C1. \<exists>C0 \<in> \<P>'. (fst C0) = C1}\<close>
            using Union_mono subsetI 
            by fastforce
          have injectivity_\<P>'_reformulated :
            \<open>\<forall>C0 C0'. ((C0 \<in> \<P>' \<and> C0' \<in> \<P>' \<and> C0' \<noteq> C0) \<longrightarrow> (fst C0) \<noteq> (fst C0'))\<close>
            unfolding \<P>'_def
            by force

          define bij_\<P>':: "('f set \<times> 'f set) \<Rightarrow> 'f set" where 
            \<open>bij_\<P>' \<equiv> fst\<close>
          have injectivity_bij_\<P>' : \<open>\<forall>C0\<in>\<P>'. \<forall>C0'\<in>\<P>'. bij_\<P>' C0 = bij_\<P>' C0' \<longrightarrow> C0 = C0'\<close>
            unfolding bij_\<P>'_def
            using injectivity_\<P>'_reformulated by blast
          then have bij_\<P>'_injectivity : \<open>inj_on bij_\<P>' \<P>'\<close>
            unfolding inj_on_def
            by simp
          moreover have surjectivity_bij_\<P>'_first_inc :  \<open>bij_\<P>' ` \<P>' \<subseteq> P\<close>
            unfolding bij_\<P>'_def
            using \<P>'_less_than_P image_subset_iff by auto
          moreover have surjectivity_bij_\<Q>'_second_inc : \<open>P \<subseteq> bij_\<P>' ` \<P>'\<close>
            unfolding bij_\<P>'_def
            using P_less_than_\<P>_reformulated by auto
          ultimately have surjectivity_bij_\<P>' : \<open>bij_\<P>' ` \<P>' = P\<close>
            by blast
          then have bij : \<open>bij_betw bij_\<P>' \<P>' P\<close>
            unfolding bij_betw_def
            using bij_\<P>'_injectivity by simp
          then have finite_\<P>' : \<open>finite \<P>'\<close>
            using bij_\<P>'_injectivity finite_P inj_on_finite surjectivity_bij_\<P>'_first_inc by auto
          moreover have \<open>\<exists>\<Q> \<subseteq> C. \<Q> = {(C1,C2). (C1,C2) \<in> C \<and> C2 \<in> Q}\<close>
            by fastforce

          then obtain \<Q> where 
            \<Q>_def: \<open>\<Q> = {(C1,C2). (C1,C2) \<in> C \<and> C2 \<in> Q}\<close>
            by auto              
          then have \<Q>_in_C : \<open>\<Q> \<subseteq> C\<close>
            by auto

          define g where
            \<open>g = (\<lambda>C2. if (\<exists>C1. (C1,C2)\<in>\<Q>) then (SOME C1. (C1,C2) \<in> \<Q>) else {})\<close>
          have \<open>\<forall>(C1,C2)\<in>\<Q>. C2\<in>Q\<close>
            using \<Q>_def by blast
          have g_stability_in_\<Q> : \<open>\<And> C1 C2. (C1,C2)\<in>\<Q> \<Longrightarrow> (g C2, C2)\<in>\<Q>\<close>
          proof -
            fix C1 C2
            show  \<open>(C1,C2)\<in>\<Q> \<Longrightarrow> (g C2, C2)\<in>\<Q>\<close>
            proof -
              assume C1_C2_in_\<Q> : \<open>(C1,C2)\<in>\<Q>\<close>
              then have \<open>\<exists>C3. (C3,C2)\<in>\<Q>\<close>
                by blast
              then have \<open>(g C2, C2) = ((SOME C1. (C1,C2) \<in> \<Q>), C2)\<close>
                unfolding g_def by simp
              then have \<open>(g C2, C2)\<in>\<Q>\<close>
                by (metis C1_C2_in_\<Q> someI_ex)
              then show  \<open>(C1,C2)\<in>\<Q> \<Longrightarrow> (g C2, C2)\<in>\<Q>\<close> by blast
            qed
          qed

          define \<Q>' where
            \<open>\<Q>' = {(g C2, C2)|C2. \<exists>C1. (C1,C2)\<in>\<Q>}\<close>
          then have injectivity_\<Q>' : \<open>\<forall>C1 C2 C1'.(((C1, C2) \<in> \<Q>' \<and> (C1', C2) \<in> \<Q>') \<longrightarrow> C1 = C1')\<close>
            by auto
          have \<Q>'_in_\<Q> : \<open>\<Q>' \<subseteq> \<Q>\<close>
            unfolding \<Q>'_def
            using g_stability_in_\<Q>
            by blast
          then have \<Q>'_in_C : \<open>\<Q>' \<subseteq> C\<close>
            using \<Q>_in_C
            by blast
          have \<Q>'_less_than_Q : \<open>\<forall>C0 \<in> \<Q>'. snd C0\<in>Q\<close>
            unfolding \<Q>'_def \<Q>_def by fastforce
          have Q_less_than_\<Q> : \<open>\<forall>C2 \<in> Q. \<exists>C1. (C1,C2)\<in>\<Q>\<close>
            unfolding \<Q>_def
            using Q_linked_C by simp
          then have Q_less_than_\<Q>_reformulated :\<open>\<forall>C2 \<in> Q. \<exists>C0\<in>\<Q>'. (snd C0) = C2\<close>
            unfolding \<Q>'_def
            by simp
          then have union_Q_in_union_fst_\<Q>' : \<open>\<Union>Q \<subseteq> \<Union>{C2. \<exists>C0 \<in> \<Q>'. (snd C0) = C2}\<close>
            using Union_mono subsetI
            by fastforce
          have injectivity_\<Q>'_reformulated :
            \<open>\<forall>C0 C0'. ((C0 \<in> \<Q>' \<and> C0' \<in> \<Q>' \<and> C0' \<noteq> C0) \<longrightarrow> (snd C0) \<noteq> (snd C0'))\<close>
            unfolding \<Q>'_def
            by force

          define bij_\<Q>':: "('f set \<times> 'f set) \<Rightarrow> 'f set" where 
            \<open>bij_\<Q>' \<equiv> snd\<close>
          have injectivity_bij_\<Q>' : \<open>\<forall>C0\<in>\<Q>'. \<forall>C0'\<in>\<Q>'. bij_\<Q>' C0 = bij_\<Q>' C0' \<longrightarrow> C0 = C0'\<close>
            unfolding bij_\<Q>'_def
            using injectivity_\<Q>'_reformulated by blast
          then have bij_\<Q>'_injectivity : \<open>inj_on bij_\<Q>' \<Q>'\<close>
            unfolding inj_on_def
            by simp
          moreover have surjectivity_bij_\<Q>'_first_inc :  \<open>bij_\<Q>' ` \<Q>' \<subseteq> Q\<close>
            unfolding bij_\<Q>'_def
            using \<Q>'_less_than_Q image_subset_iff by auto
          moreover have surjectivity_bij_\<Q>'_second_inc : \<open>Q \<subseteq> bij_\<Q>' ` \<Q>'\<close>
            unfolding bij_\<Q>'_def
            using Q_less_than_\<Q>_reformulated by auto
          ultimately have surjectivity_bij_\<Q>' : \<open>bij_\<Q>' ` \<Q>' = Q\<close>
            by blast
          then have bij : \<open>bij_betw bij_\<Q>' \<Q>' Q\<close>
            unfolding bij_betw_def
            using bij_\<Q>'_injectivity by simp
          then have finite_\<Q>' : \<open>finite \<Q>'\<close>
            using bij_\<Q>'_injectivity finite_Q inj_on_finite surjectivity_bij_\<Q>'_first_inc by auto

          have not_empty_\<P>_or_\<Q> : \<open>\<P> \<noteq> {} \<or> \<Q> \<noteq> {}\<close>
            using \<P>'_in_\<P> \<Q>'_in_\<Q> surjectivity_bij_\<P>' surjectivity_bij_\<Q>' not_empty_P_or_Q 
            by fastforce
          then have not_empty_\<P>'_or_\<Q>' : \<open>\<P>' \<noteq> {} \<or> \<Q>' \<noteq> {}\<close>
            using not_empty_P_or_Q surjectivity_bij_\<P>' surjectivity_bij_\<Q>' by blast

          define \<R>' where \<open>\<R>' = \<P>'\<union>\<Q>'\<close>
          have \<open>\<forall> (C1,C2) \<in> \<R>'. C1\<in>P \<or> C2\<in>Q\<close>
            unfolding \<R>'_def \<P>'_def \<Q>'_def \<P>_def \<Q>_def
            by fastforce
          have finite_\<R>' : \<open>finite \<R>'\<close>
            unfolding \<R>'_def
            using finite_\<P>' finite_\<Q>' by simp
          moreover have \<R>'_in_C : \<open>\<R>' \<subseteq> C\<close>
            unfolding \<R>'_def
            using \<P>'_in_C \<Q>'_in_C
            by blast
          moreover have not_empty_\<R>' : \<open>\<R>' \<noteq> {}\<close>
            using \<R>'_def not_empty_\<P>'_or_\<Q>' by blast

          have max_\<R>' : \<open>\<exists>(M0,N0)\<in>\<R>'. (\<forall>(M,N)\<in>\<R>'. (M,N) \<preceq>\<^sub>s (M0,N0))\<close>
          proof (rule ccontr) 
            assume \<open>\<not>(\<exists>(M0,N0)\<in>\<R>'. (\<forall>(M,N)\<in>\<R>'. (M,N) \<preceq>\<^sub>s (M0,N0)))\<close>
            then have abs_max_\<R>' : \<open>\<forall>(M0,N0)\<in>\<R>'. (\<exists>(M,N)\<in>\<R>'. \<not>((M,N) \<preceq>\<^sub>s (M0,N0)))\<close>
              by auto
            have \<open>\<forall>(M0,N0)\<in>C. \<forall>(M,N)\<in>C. 
                  \<not>((M,N),(M0,N0))\<in>zorn_relation \<longrightarrow> ((M0,N0),(M,N))\<in>zorn_relation\<close>
              unfolding zorn_relation_def
              using C_chain
              by (smt (verit, best) Chains_def case_prodI2 mem_Collect_eq zorn_relation_def)
            then have \<open>\<forall>(M0,N0)\<in>C. \<forall>(M,N)\<in>C. \<not>(M,N) \<preceq>\<^sub>s (M0,N0) \<longrightarrow> (M0,N0) \<preceq>\<^sub>s (M,N)\<close>
              unfolding zorn_relation_def
              using trivial_replacement_order
              by blast
            then have \<open>\<forall>(M0,N0)\<in>\<R>'. \<forall>(M,N)\<in>\<R>'. \<not>(M,N) \<preceq>\<^sub>s (M0,N0) \<longrightarrow> (M0,N0) \<preceq>\<^sub>s (M,N)\<close>
              using \<R>'_in_C
              by auto
            then have \<open>\<forall>(M0,N0)\<in>\<R>'. \<forall>(M,N)\<in>\<R>'. \<not>(M,N) \<preceq>\<^sub>s (M0,N0) \<longrightarrow> (M0,N0) \<prec>\<^sub>s (M,N)\<close>
              unfolding  order_double_subsets_strict_def
              by blast
            then have abs_max_\<R>'_reformulated : \<open>\<forall>(M0,N0)\<in>\<R>'. (\<exists>(M,N)\<in>\<R>'. (M0,N0) \<prec>\<^sub>s (M,N))\<close>
              using abs_max_\<R>'
              by blast
            (* For all (M0,N0), find_dif returns a pair (M,N) which is \<succ> (M0,N0)*)
            define  find_dif :: "('f set \<times> 'f set) \<Rightarrow> ('f set \<times> 'f set)" where 
              \<open>find_dif = (\<lambda>(M0,N0). if (\<exists>(M,N)\<in>\<R>'. (M0,N0) \<prec>\<^sub>s (M,N)) 
                                     then (SOME (M,N). (M,N)\<in>\<R>' \<and> (M0,N0) \<prec>\<^sub>s (M,N)) 
                                     else ({},{}))\<close>
            obtain M0 N0 where M0_N0_def : \<open>(M0,N0)\<in> \<R>'\<close>
              using not_empty_\<R>' by auto
            define bij_nat :: "nat \<Rightarrow> ('f set \<times> 'f set)" where
              \<open>bij_nat \<equiv> \<lambda>k. (find_dif^^k) (M0, N0)\<close>
            have bij_nat_in_\<R>' : \<open>bij_nat k \<in> \<R>'\<close> for k
            proof (induction k)
              case 0
              then show ?case
                unfolding bij_nat_def
                using M0_N0_def
                by simp
            next
              case (Suc k)
              assume \<open>bij_nat k \<in> \<R>'\<close>
              have new_major_k : \<open>\<exists>(M,N)\<in>\<R>'. bij_nat k \<prec>\<^sub>s (M,N)\<close>
                using abs_max_\<R>'_reformulated Suc
                by simp
              then have \<open>find_dif (bij_nat k) = (SOME (M,N). (M,N)\<in>\<R>' \<and> bij_nat k \<prec>\<^sub>s (M,N))\<close>
                unfolding find_dif_def
                by auto
              then have \<open>bij_nat (Suc k) = (SOME (M,N). (M,N)\<in>\<R>' \<and> bij_nat k \<prec>\<^sub>s (M,N))\<close>
                unfolding bij_nat_def
                by simp
              then show ?case
                by (metis (mono_tags, lifting) new_major_k case_prod_conv some_eq_imp surj_pair)
            qed
            then have new_major_general : \<open>\<exists>(M,N)\<in>\<R>'. (bij_nat k) \<prec>\<^sub>s (M,N)\<close> for k
              using abs_max_\<R>'_reformulated
              by simp
            then have \<open>find_dif (bij_nat k) = (SOME (M,N). (M,N)\<in>\<R>' \<and> bij_nat k \<prec>\<^sub>s (M,N))\<close> for k
              unfolding find_dif_def
              by auto
            then have \<open>bij_nat k \<prec>\<^sub>s find_dif (bij_nat k)\<close> for k
              by (metis (mono_tags, lifting) case_prod_conv new_major_general some_eq_imp surj_pair)
            then have bij_nat_croiss: \<open>(bij_nat (k::nat)) \<prec>\<^sub>s (bij_nat (Suc k))\<close> for k
              using bij_nat_def by simp
            have bij_nat_general_croiss : \<open>i < j \<Longrightarrow> bij_nat i \<prec>\<^sub>s bij_nat j\<close> for i j
            proof -
              assume hyp_croiss : \<open>i < j\<close>
              have \<open>bij_nat i \<prec>\<^sub>s bij_nat (i+1+(k::nat))\<close> for k
              proof (induction k)
                case 0
                then show ?case using bij_nat_croiss by simp
              next
                case (Suc k)
                have \<open>bij_nat (i+1+k) \<prec>\<^sub>s bij_nat (i+1+(Suc k))\<close>
                  using bij_nat_croiss by simp
                then show ?case using zorn_strict_relation_trans Suc by blast
              qed

              then have \<open>bij_nat i \<prec>\<^sub>s bij_nat j\<close>
                by (metis Suc_eq_plus1_left hyp_croiss add.assoc add.commute less_natE)
              then show ?thesis by simp
            qed

            have \<open>bij_nat i = bij_nat j \<and> \<not>i=j \<Longrightarrow> False\<close> for i j
            proof -
              assume bij_nat_i_equals_bij_nat_j : \<open>bij_nat i = bij_nat j \<and> \<not>i=j\<close>
              then have \<open>i < j \<or> j < i\<close>
                by auto
              then have \<open>bij_nat i \<prec>\<^sub>s bij_nat j \<or> bij_nat j \<prec>\<^sub>s bij_nat i\<close>
                using bij_nat_general_croiss
                by blast
              then have \<open>bij_nat i \<noteq> bij_nat j\<close>
                unfolding order_double_subsets_strict_def
                by force
              then show ?thesis 
                using bij_nat_i_equals_bij_nat_j by simp
            qed

            then have bij_nat_inj : \<open>bij_nat i = bij_nat j \<longrightarrow> i = j\<close> for i j
              unfolding bij_nat_def
              by auto
            then have bij_nat_inj_gen : \<open>\<forall> i j. bij_nat i = bij_nat j \<longrightarrow> i = j\<close>
              by auto
            then have \<open>inj_on bij_nat (UNIV :: nat set)\<close>
              unfolding inj_on_def
              by simp
            then have bij_nat_is_a_bij : 
                     \<open>bij_betw bij_nat (UNIV :: nat set) (bij_nat `(UNIV :: nat set))\<close>
              unfolding bij_betw_def
              by simp
            then have \<open>finite (UNIV :: nat set) \<longleftrightarrow> finite (bij_nat `(UNIV:: nat set))\<close>
              using bij_betw_finite by auto
            moreover have \<open>\<not>(finite (UNIV :: nat set))\<close>
              by simp
            ultimately have \<open>\<not>finite (bij_nat `(UNIV:: nat set))\<close>
              by blast
            moreover have \<open>bij_nat `(UNIV:: nat set) \<subseteq> \<R>'\<close>
              unfolding bij_nat_def
              using \<R>'_in_C bij_nat_in_\<R>' image_subset_iff bij_nat_def
              by blast
            ultimately have \<open>\<not>(finite \<R>')\<close>
              using finite_subset by blast
            then show "False" using finite_\<R>' by blast
          qed

          then obtain M_max N_max where
            M_N_max_def : \<open>(M_max,N_max)\<in>\<R>' \<and> (\<forall>(M,N)\<in>\<R>'. (M,N) \<preceq>\<^sub>s (M_max,N_max))\<close>
            by auto
          then have  \<open>\<forall>C1\<in>P. \<exists>(M0,N0)\<in>\<R>'. M0 = C1 \<close>
            using \<R>'_def P_less_than_\<P>_reformulated by fastforce
          then have \<open>\<Union>P \<subseteq> \<Union>{C1. \<exists>C0 \<in> \<R>'. (fst C0) = C1}\<close>
            unfolding \<R>'_def        
            by fastforce
          moreover have \<open>\<forall>C1. (\<exists>C0 \<in> \<R>'. (fst C0) = C1 \<and> C0 \<preceq>\<^sub>s (M_max,N_max)) \<longrightarrow> C1 \<subseteq> M_max\<close>
            unfolding M_N_max_def order_double_subsets_def
            by auto
          then have \<open>\<forall>C1 \<in> {C1. \<exists>C0 \<in> \<R>'. (fst C0) = C1}. C1 \<subseteq> M_max \<close>
            using M_N_max_def by auto
          then have \<open>\<Union>{C1. \<exists>C0 \<in> \<R>'. (fst C0) = C1} \<subseteq> M_max\<close>
            by auto
          ultimately have union_P_in_M_max : \<open>\<Union>P \<subseteq> M_max\<close>
            by blast
          moreover have \<open>\<forall>C2\<in>Q. \<exists>(M0,N0)\<in>\<R>'. N0 = C2 \<close>
            using \<R>'_def Q_less_than_\<Q>_reformulated by fastforce
          then have \<open>\<Union>Q \<subseteq> \<Union>{C2. \<exists>C0 \<in> \<R>'. (snd C0) = C2}\<close>
            unfolding \<R>'_def        
            by fastforce
          moreover have \<open>\<forall>C2. (\<exists>C0 \<in> \<R>'. (snd C0) = C2 \<and> C0 \<preceq>\<^sub>s (M_max,N_max)) \<longrightarrow> C2 \<subseteq> N_max\<close>
            unfolding M_N_max_def order_double_subsets_def
            by auto
          then have \<open>\<forall>C2 \<in> {C2. \<exists>C0 \<in> \<R>'. (snd C0) = C2}. C2 \<subseteq> N_max \<close>
            using M_N_max_def by auto
          then have \<open>\<Union>{C2. \<exists>C0 \<in> \<R>'. (snd C0) = C2} \<subseteq> N_max\<close>
            by auto
          ultimately have union_Q_in_N_max : \<open>\<Union>Q \<subseteq> N_max\<close>
            by blast
          have \<open>M' \<subseteq> M_max \<and> N' \<subseteq> N_max\<close>
            using P_supset Q_supset union_P_in_M_max union_Q_in_N_max by auto
          then have \<open>M_max \<Turnstile> N_max\<close>
            using abs_max_chain_compactness entails_subsets
            by force
          moreover have \<open>(M_max,N_max) \<in> \<R>'\<close>
            using M_N_max_def
            by simp
          then have \<open>(M_max,N_max) \<in> C\<close>
            using \<R>'_in_C by auto
          then have \<open>(M_max,N_max) \<in> A\<close>
            using C_chain relation_in_A by auto
          then have \<open>\<not>M_max \<Turnstile> N_max\<close>
            unfolding A_def
            by auto
          ultimately show "False"
            by simp
        qed
      qed
    qed
    moreover have \<open>\<And>C. C \<in> Chains zorn_relation \<Longrightarrow> M \<subseteq> fst (max_chain C)\<close>
      using M_N_less_than_max_chain order_double_subsets_def fst_eqD
      by metis
    moreover have \<open>\<And>C. C \<in> Chains zorn_relation \<Longrightarrow> N \<subseteq> snd (max_chain C)\<close>
      using M_N_less_than_max_chain order_double_subsets_def snd_eqD
      by metis      
    ultimately have max_chain_in_A : \<open>\<And>C. C \<in> Chains zorn_relation \<Longrightarrow> max_chain C \<in> A\<close>
      unfolding A_def using M_N_less_than_max_chain case_prod_beta
      by force

(*reformulation of max_chain_in_A to apply Zorn's lemma*)
    then have \<open>\<And>C. C \<in> Chains zorn_relation \<Longrightarrow> 
      (max_chain C) \<in> A \<and> (\<forall>C0\<in>C. (C0, max_chain C) \<in> zorn_relation)\<close>
      unfolding zorn_relation_def
      using zorn_relation_field_is_A max_chain_is_a_max relation_in_A zorn_relation_def
      by fastforce
    then have zorn_hypothesis_u : 
      \<open>\<And>C. C \<in> Chains zorn_relation \<Longrightarrow> \<exists>u\<in>Field zorn_relation. \<forall>a\<in>C. (a, u) \<in> zorn_relation\<close>
      using zorn_relation_field_is_A  max_chain_is_a_max by auto

(*application of Zorn's lemma*)
    then have  \<open>\<exists>Cmax\<in>Field zorn_relation. \<forall>C\<in>Field zorn_relation. 
                (Cmax, C) \<in> zorn_relation \<longrightarrow> C = Cmax\<close>
      using Zorns_po_lemma zorn_hypothesis_u zorn_hypothesis_po by blast 
    then have zorn_result : \<open>\<exists>Cmax\<in>A. \<forall>C\<in>A. (Cmax, C) \<in> zorn_relation \<longrightarrow> C = Cmax\<close>
      using zorn_relation_field_is_A by blast
    then obtain Cmax where 
      Cmax_in_A : \<open>Cmax\<in>A\<close> and 
      Cmax_is_max : \<open>\<forall>C\<in>A. (Cmax, C) \<in> zorn_relation \<longrightarrow> C = Cmax\<close>
      by blast

(*deriving contrapos_hyp_entails_sup from Zorn's lemma*)
    have Cmax_not_entails : \<open>\<not> fst Cmax \<Turnstile> snd Cmax\<close>
      unfolding A_def
      using Cmax_in_A
      using A_def by force
    have M_less_fst_Cmax : \<open>M \<subseteq> fst Cmax\<close>
      using A_def Cmax_in_A  by force
    moreover have N_less_snd_Cmax : \<open>N \<subseteq> snd Cmax\<close>
      using A_def Cmax_in_A  by force
    have \<open>fst Cmax \<union> snd Cmax = UNIV\<close>
    proof (rule ccontr)
      assume \<open>\<not>fst Cmax \<union> snd Cmax = UNIV\<close>
      then have \<open>\<exists>C0. C0 \<notin> fst Cmax \<union> snd Cmax\<close>
        by auto
      then obtain C0 where C0_def : \<open>C0 \<notin> fst Cmax \<union> snd Cmax\<close>
        by auto
      have fst_max_entailment_extended : \<open>(fst Cmax) \<union> {C0} \<Turnstile> snd Cmax\<close>
      proof (rule ccontr)
        assume \<open>\<not>(fst Cmax) \<union> {C0} \<Turnstile> snd Cmax\<close>
        then have fst_extended_Cmax_in_A : \<open>((fst Cmax \<union> {C0}), snd Cmax) \<in> A\<close>
          unfolding A_def
          using M_less_fst_Cmax N_less_snd_Cmax by blast
        then have \<open>(Cmax,((fst Cmax) \<union> {C0},snd Cmax)) \<in> zorn_relation\<close>
          unfolding zorn_relation_def order_double_subsets_def
          using Cmax_in_A by auto
        then have \<open>Cmax = ((fst Cmax) \<union> {C0},snd Cmax)\<close>
          using Cmax_is_max fst_extended_Cmax_in_A by fastforce
        then have \<open>C0 \<in> (fst Cmax)\<close>
          by (metis UnI2 fst_eqD singleton_iff)
        then show "False" using C0_def by auto
      qed
      moreover have snd_max_entailment_extended : \<open>fst Cmax \<Turnstile> snd Cmax \<union> {C0}\<close>
      proof (rule ccontr)
        assume \<open>\<not>fst Cmax \<Turnstile> snd Cmax \<union> {C0}\<close>
        then have snd_extended_Cmax_in_A : \<open>(fst Cmax,snd Cmax \<union> {C0}) \<in> A\<close>
          unfolding A_def
          using M_less_fst_Cmax N_less_snd_Cmax by blast
        then have \<open>(Cmax,(fst Cmax,snd Cmax \<union> {C0})) \<in> zorn_relation\<close>
          unfolding zorn_relation_def order_double_subsets_def
          using Cmax_in_A by auto
        then have \<open>Cmax = (fst Cmax,snd Cmax \<union> {C0})\<close>
          using Cmax_is_max snd_extended_Cmax_in_A by fastforce
        then have \<open>C0 \<in> (snd Cmax)\<close>
          by (metis UnI2 singleton_iff sndI)
        then show "False" using C0_def by auto
      qed
      ultimately have \<open>fst Cmax \<Turnstile> snd Cmax\<close>
        using entails_cut by force
      then have \<open>Cmax \<notin> A\<close>
        unfolding A_def
        by fastforce
      then show "False"
        using Cmax_in_A by simp
    qed
    then show ?thesis using M_less_fst_Cmax N_less_snd_Cmax Cmax_not_entails by auto
  qed
  then show "False" using hyp_entails_sup by auto
qed


 
lemma entails_each: "M \<Turnstile> P \<Longrightarrow> \<forall>C\<in>M. N \<Turnstile> Q \<union> {C} \<Longrightarrow> \<forall>D\<in>P. N \<union> {D} \<Turnstile> Q \<Longrightarrow> N \<Turnstile> Q" 
proof -
  fix M P N Q
  assume m_entails_p: \<open>M \<Turnstile> P\<close>
    and n_to_q_m: \<open>\<forall>C\<in>M. N \<Turnstile> Q \<union> {C}\<close>
    and n_p_to_q: \<open>\<forall>D\<in>P. N \<union> {D} \<Turnstile> Q\<close>
  have \<open>\<forall>M' N'. (M' \<supseteq> N \<and> N' \<supseteq> Q \<and> M' \<union> N' = UNIV) \<longrightarrow> M' \<Turnstile> N'\<close>
  proof clarsimp
    fix M' N'
    assume n_sub_mp: \<open>M' \<supseteq> N\<close> and
      q_sub_np: \<open>N' \<supseteq> Q\<close> and
      union_univ: \<open>M' \<union> N' = UNIV\<close>
    consider (a) "\<not> (M' \<inter> P = {})" | (b) "\<not> (N' \<inter> M = {})" | (c) "P \<subseteq> N' \<and> M \<subseteq> M'"
      using union_univ by auto 
    then show \<open>M' \<Turnstile> N'\<close>
    proof cases
      case a
      assume \<open>M' \<inter> P \<noteq> {}\<close>
      then obtain D where d_in: \<open>D \<in> M' \<inter> P\<close> by auto
      then have \<open>N \<union> {D} \<subseteq> M'\<close> using n_sub_mp by auto
      moreover have \<open>N \<union> {D} \<Turnstile> Q\<close> using n_p_to_q d_in by blast
      ultimately show ?thesis
        using entails_subsets[OF _ q_sub_np] by blast
    next
      case b
      assume \<open>N' \<inter> M \<noteq> {}\<close>
      then obtain C where c_in: \<open>C \<in> M \<inter> N'\<close> by auto
      then have \<open>Q \<union> {C} \<subseteq> N'\<close> using q_sub_np by auto
      moreover have \<open>N \<Turnstile> Q \<union> {C}\<close> using n_to_q_m c_in by blast
      ultimately show ?thesis
        using entails_subsets[OF n_sub_mp] by blast
    next
      case c
      then show ?thesis
        using entails_subsets[OF _ _ m_entails_p] by simp
    qed      
  qed
  then show \<open>N \<Turnstile> Q\<close>
    using entails_supsets by simp
qed


lemma entails_bot_to_entails_empty: \<open>{} \<Turnstile> {bot} \<Longrightarrow> {} \<Turnstile> {}\<close>
  using entails_reflexive[of bot] entails_each[of "{}" "{bot}" "{}" "{}"] bot_entails_empty
  by auto

abbreviation equi_entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" where
  "equi_entails M N \<equiv> (M \<Turnstile> N \<and> N \<Turnstile> M)"

lemma entails_cond_reflexive: \<open>N \<noteq> {} \<Longrightarrow> N \<Turnstile> N\<close>
  using entails_reflexive entails_subsets by (meson bot.extremum from_nat_into insert_subset)
    
  (* This lemma shows that an entailment such that {} \<Turnstile> {} is useless, it may or may not help better
  understand what this entailment is depending on who you ask ^_^' *)
lemma entails_empty_reflexive_dangerous: \<open>{} \<Turnstile> {} \<Longrightarrow> M \<Turnstile> N\<close>
  using entails_subsets[of "{}" M "{}" N] by simp

definition entails_conjunctive :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>\<inter>" 50) where
  "M \<Turnstile>\<inter> N \<equiv> \<forall>C\<in>N. M \<Turnstile> {C}"

sublocale Calculus.consequence_relation "{bot}" "(\<Turnstile>\<inter>)"
proof
  show "{bot} \<noteq> {}" by simp
next
  fix B N
  assume b_in: "B \<in> {bot}"
  then have b_is: "B = bot" by simp
  show "{B} \<Turnstile>\<inter> N"
    unfolding entails_conjunctive_def
    using entails_subsets[of "{B}" "{B}" "{}"] b_is bot_entails_empty by blast
next
  fix M N
  assume m_subs: "(M :: 'f set) \<subseteq> N"
  show \<open>N \<Turnstile>\<inter> M\<close> unfolding entails_conjunctive_def
  proof
    fix C
    assume "C \<in> M"
    then have c_subs: \<open>{C} \<subseteq> N\<close> using m_subs by fast
    show \<open>N \<Turnstile> {C}\<close> using entails_subsets[OF c_subs _ entails_reflexive[of C]] by simp 
  qed
next
  fix M N
  assume \<open>\<forall>C\<in>M. N \<Turnstile>\<inter> {C}\<close>
  then show \<open>N \<Turnstile>\<inter> M\<close>
    unfolding entails_conjunctive_def by blast
next
  fix M N P
  assume
    trans1: \<open>M \<Turnstile>\<inter> N\<close> and
    trans2: \<open>N \<Turnstile>\<inter> P\<close>
  show \<open>M \<Turnstile>\<inter> P\<close> unfolding entails_conjunctive_def
  proof
    fix C
    assume \<open>C \<in> P\<close>
    then have n_to_c: \<open>N \<Turnstile> {C}\<close> using trans2 unfolding entails_conjunctive_def by simp
    have "M \<union> {C} \<Turnstile> {C}"
      using entails_subsets[OF _ _ entails_reflexive[of C], of "M \<union> {C}" "{C}"] by fast
    then have m_c_to_c: \<open>\<forall>D\<in>{C}. M \<union> {D} \<Turnstile> {C}\<close> by blast
    have m_to_c_n: "\<forall>D\<in>N. M \<Turnstile> {C} \<union> {D}"
      using trans1 entails_subsets[of M M] unfolding entails_conjunctive_def by blast 
    show \<open>M \<Turnstile> {C}\<close>
      using entails_each[OF n_to_c m_to_c_n m_c_to_c] unfolding entails_conjunctive_def .
  qed
qed

definition entails_neg :: "'f sign set \<Rightarrow> 'f sign set \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<sim>" 50) where
  "entails_neg M N \<equiv> {C. Pos C \<in> M} \<union> {C. Neg C \<in> N} \<Turnstile> {C. Pos C \<in> N} \<union> {C. Neg C \<in> M}"

lemma ext_cons_rel: \<open>consequence_relation (Pos bot) entails_neg\<close>
proof
  show "entails_neg {Pos bot} {}"
    unfolding entails_neg_def using bot_entails_empty by simp
next
  fix C
  show \<open>entails_neg {C} {C}\<close>
    unfolding entails_neg_def using entails_cond_reflexive
    by (metis (mono_tags, lifting) Un_empty empty_Collect_eq insert_iff is_Pos.cases) 
next
  fix M N P Q
  assume
    subs1: "M \<subseteq> N" and
    subs2: "P \<subseteq> Q" and
    entails1: "entails_neg M P"
  have union_subs1: \<open>{C. Pos C \<in> M} \<union> {C. Neg C \<in> P} \<subseteq> {C. Pos C \<in> N} \<union> {C. Neg C \<in> Q}\<close>
    using subs1 subs2 by auto
  have union_subs2: \<open>{C. Pos C \<in> P} \<union> {C. Neg C \<in> M} \<subseteq> {C. Pos C \<in> Q} \<union> {C. Neg C \<in> N}\<close>
    using subs1 subs2 by auto
  have union_entails1: "{C. Pos C \<in> M} \<union> {C. Neg C \<in> P} \<Turnstile> {C. Pos C \<in> P} \<union> {C. Neg C \<in> M}"
    using entails1 unfolding entails_neg_def .
  show \<open>entails_neg N Q\<close>
    using entails_subsets[OF union_subs1 union_subs2 union_entails1] unfolding entails_neg_def .
next
  fix M N C M' N'
  assume cut_hypothesis_M_N: \<open>M \<Turnstile>\<^sub>\<sim> N \<union> {C}\<close> and
         cut_hypothesis_M'_N': \<open>M' \<union> {C} \<Turnstile>\<^sub>\<sim> N'\<close>
  consider (a) \<open>is_Pos C\<close> | (b) \<open>\<not>is_Pos C\<close>
    by auto
  then show \<open>M \<union> M' \<Turnstile>\<^sub>\<sim> N \<union> N'\<close>
  proof (cases)
    case a
    assume Neg_C: \<open>is_Pos C\<close>
    have M_entails_NC:
          \<open>{D. Pos D \<in> M} \<union> {D. Neg D \<in> N \<union> {C}} \<Turnstile> {D. Pos D \<in> N \<union> {C}} \<union> {D. Neg D \<in> M}\<close>
      using cut_hypothesis_M_N entails_neg_def by force
    moreover have \<open>{D. Pos D \<in> M} \<union> {D. Neg D \<in> N \<union> {C}} = {D. Pos D \<in> M} \<union> {D. Neg D \<in> N}\<close>
      using Neg_C by force
    ultimately have \<open>{D. Pos D \<in> M} \<union> {D. Neg D \<in> N} \<Turnstile> {D. Pos D \<in> N \<union> {C}} \<union> {D. Neg D \<in> M}\<close>
      by simp
    moreover have \<open>{D. Pos D \<in> N \<union> {C}} \<union> {D. Neg D \<in> M} =
        {D. Pos D \<in> N} \<union> {to_V C} \<union> {D. Neg D \<in> M}\<close>
      using is_Pos_to_V[OF Neg_C] by force
    ultimately have M_entails_NC_reformulated:
          \<open>{D. Pos D \<in> M} \<union> {D. Neg D \<in> N} \<Turnstile> {D. Pos D \<in> N} \<union> {to_V C} \<union> {D. Neg D \<in> M}\<close>
      by simp
    have M'_entails_N'C:
          \<open>{D. Pos D \<in> M' \<union> {C}} \<union> {D. Neg D \<in> N'} \<Turnstile> {D. Pos D \<in> N'} \<union> {D. Neg D \<in> M' \<union> {C}}\<close>
      using cut_hypothesis_M'_N' entails_neg_def by force
    moreover have \<open>{D. Pos D \<in> M' \<union> {C}} \<union> {D. Neg D \<in> N'} =
                    {D. Pos D \<in> M'} \<union> {to_V C} \<union> {D. Neg D \<in> N'}\<close>
      using is_Pos_to_V[OF Neg_C] by force
    ultimately have \<open>{D. Pos D \<in> M'} \<union> {to_V C} \<union> {D. Neg D \<in> N'} \<Turnstile>
        {D. Pos D \<in> N'} \<union> {D. Neg D \<in> M' \<union> {C}}\<close>
      by simp
    moreover have \<open>{D. Pos D \<in> N'} \<union> {D. Neg D \<in> M' \<union> {C}} = {D. Pos D \<in> N'} \<union> {D. Neg D \<in> M'}\<close>
      using Neg_C by force
    ultimately have M'_entails_N'C_reformulated:
          \<open>{D. Pos D \<in> M'} \<union> {to_V C} \<union> {D. Neg D \<in> N'} \<Turnstile> {D. Pos D \<in> N'} \<union> {D. Neg D \<in> M'}\<close>
      by simp
    have \<open>{D. Pos D \<in> M} \<union> {D. Neg D \<in> N} \<union> {D. Pos D \<in> M'}  \<union> {D. Neg D \<in> N'}\<Turnstile>
          {D. Pos D \<in> N} \<union> {D. Neg D \<in> M} \<union> {D. Pos D \<in> N'} \<union> {D. Neg D \<in> M'}\<close>
      using M_entails_NC_reformulated M'_entails_N'C_reformulated entails_cut
      by (smt (verit, ccfv_threshold) M'_entails_N'C_reformulated 
          M_entails_NC_reformulated Un_assoc Un_commute)
    moreover have  \<open>{D. Pos D \<in> M} \<union> {D. Neg D \<in> N} \<union> {D. Pos D \<in> M'}  \<union> {D. Neg D \<in> N'} = 
                    {D. Pos D \<in> M \<union> M'} \<union> {D. Neg D \<in> N \<union> N'}\<close>
      by auto
    ultimately have \<open>{D. Pos D \<in> M \<union> M'} \<union> {D. Neg D \<in> N \<union> N'} \<Turnstile>
                     {D. Pos D \<in> N} \<union> {D. Neg D \<in> M} \<union> {D. Pos D \<in> N'} \<union> {D. Neg D \<in> M'}\<close>
      by simp
    moreover have \<open>{D. Pos D \<in> N} \<union> {D. Neg D \<in> M} \<union> {D. Pos D \<in> N'} \<union> {D. Neg D \<in> M'} =
                   {D. Pos D \<in> N \<union> N'} \<union> {D. Neg D \<in> M \<union> M'}\<close>
      by auto
    ultimately have \<open>{D. Pos D \<in> M \<union> M'} \<union> {D. Neg D \<in> N \<union> N'} \<Turnstile>
                     {D. Pos D \<in> N \<union> N'} \<union> {D. Neg D \<in> M \<union> M'}\<close>
      by simp 
    then show ?thesis unfolding entails_neg_def by auto
  next
    case b
    assume Neg_C: \<open>\<not>is_Pos C\<close>
    have M_entails_NC:
          \<open>{D. Pos D \<in> M} \<union> {D. Neg D \<in> N \<union> {C}} \<Turnstile> {D. Pos D \<in> N \<union> {C}} \<union> {D. Neg D \<in> M}\<close>
      using cut_hypothesis_M_N entails_neg_def by force
    moreover have \<open>{D. Pos D \<in> M} \<union> {D. Neg D \<in> N \<union> {C}} =
                   {D. Pos D \<in> M} \<union> {to_V C} \<union> {D. Neg D \<in> N}\<close>
      using is_Neg_to_V[OF Neg_C] by force
    ultimately have \<open>{D. Pos D \<in> M} \<union> {to_V C} \<union> {D. Neg D \<in> N} \<Turnstile>
          {D. Pos D \<in> N \<union> {C}} \<union> {D. Neg D \<in> M}\<close>
      by simp
    moreover have \<open>{D. Pos D \<in> N \<union> {C}} \<union> {D. Neg D \<in> M} = {D. Pos D \<in> N} \<union> {D. Neg D \<in> M}\<close>
      using Neg_C by force
    ultimately have M_entails_NC_reformulated:
          \<open>{D. Pos D \<in> M} \<union> {to_V C} \<union> {D. Neg D \<in> N} \<Turnstile> {D. Pos D \<in> N} \<union> {D. Neg D \<in> M}\<close>
      by simp
    have M'_entails_N'C:
          \<open>{D. Pos D \<in> M' \<union> {C}} \<union> {D. Neg D \<in> N'} \<Turnstile> {D. Pos D \<in> N'} \<union> {D. Neg D \<in> M' \<union> {C}}\<close>
      using cut_hypothesis_M'_N' entails_neg_def by force
    moreover have \<open>{D. Pos D \<in> M' \<union> {C}} \<union> {D. Neg D \<in> N'} = {D. Pos D \<in> M'} \<union> {D. Neg D \<in> N'}\<close>
      using Neg_C by force
    ultimately have \<open>{D. Pos D \<in> M'} \<union> {D. Neg D \<in> N'} \<Turnstile> {D. Pos D \<in> N'} \<union> {D. Neg D \<in> M' \<union> {C}}\<close>
      by simp
    moreover have \<open>{D. Pos D \<in> N'} \<union> {D. Neg D \<in> M' \<union> {C}} =
                     {D. Pos D \<in> N'} \<union> {to_V C} \<union> {D. Neg D \<in> M'}\<close>
      using is_Neg_to_V[OF Neg_C] by force
    ultimately have M'_entails_N'C_reformulated:
          \<open>{D. Pos D \<in> M'} \<union> {D. Neg D \<in> N'} \<Turnstile> {D. Pos D \<in> N'} \<union> {to_V C} \<union> {D. Neg D \<in> M'}\<close>
      by simp
    have \<open>{D. Pos D \<in> M} \<union> {D. Neg D \<in> N} \<union> {D. Pos D \<in> M'}  \<union> {D. Neg D \<in> N'}\<Turnstile>
          {D. Pos D \<in> N} \<union> {D. Neg D \<in> M} \<union> {D. Pos D \<in> N'} \<union> {D. Neg D \<in> M'}\<close>
      using M_entails_NC_reformulated M'_entails_N'C_reformulated entails_cut
      by (smt (verit, ccfv_threshold) M'_entails_N'C_reformulated 
          M_entails_NC_reformulated Un_assoc Un_commute)
    moreover have  \<open>{D. Pos D \<in> M} \<union> {D. Neg D \<in> N} \<union> {D. Pos D \<in> M'}  \<union> {D. Neg D \<in> N'} = 
                    {D. Pos D \<in> M \<union> M'} \<union> {D. Neg D \<in> N \<union> N'}\<close>
      by auto
    ultimately have \<open>{D. Pos D \<in> M \<union> M'} \<union> {D. Neg D \<in> N \<union> N'} \<Turnstile>
                     {D. Pos D \<in> N} \<union> {D. Neg D \<in> M} \<union> {D. Pos D \<in> N'} \<union> {D. Neg D \<in> M'}\<close>
      by simp
    moreover have \<open>{D. Pos D \<in> N} \<union> {D. Neg D \<in> M} \<union> {D. Pos D \<in> N'} \<union> {D. Neg D \<in> M'} =
                   {D. Pos D \<in> N \<union> N'} \<union> {D. Neg D \<in> M \<union> M'}\<close>
      by auto
    ultimately have \<open>{D. Pos D \<in> M \<union> M'} \<union> {D. Neg D \<in> N \<union> N'} \<Turnstile>
                     {D. Pos D \<in> N \<union> N'} \<union> {D. Neg D \<in> M \<union> M'}\<close>
      by simp 
    then show ?thesis unfolding entails_neg_def by auto
  qed
next
  fix M N
  assume M_entails_N: \<open>M \<Turnstile>\<^sub>\<sim> N\<close>
  then have \<open>{C. Pos C \<in> M} \<union> {C. Neg C \<in> N} \<Turnstile> {C. Pos C \<in> N} \<union> {C. Neg C \<in> M}\<close>
    unfolding entails_neg_def .
  then have \<open>\<exists> M' N'. (M' \<subseteq> {C. Pos C \<in> M} \<union> {C. Neg C \<in> N} \<and>
                       N' \<subseteq> {C. Pos C \<in> N} \<union> {C. Neg C \<in> M} \<and> 
                       finite M' \<and> finite N' \<and> M' \<Turnstile> N')\<close>
    using entails_compactness by auto
  then obtain M' N' where
    M'_def: \<open>M' \<subseteq> {C. Pos C \<in> M} \<union> {C. Neg C \<in> N}\<close> and
    M'_finite: \<open>finite M'\<close> and
    N'_def: \<open>N' \<subseteq> {C. Pos C \<in> N} \<union> {C. Neg C \<in> M}\<close> and
    N'_finite: \<open>finite N'\<close> and
    M'_entails_N': \<open>M' \<Turnstile> N'\<close>
    by auto
  define M'_pos where "M'_pos = M' \<inter> {C. Pos C \<in> M}"
  define M'_neg where "M'_neg = M' \<inter> {C. Neg C \<in> N}"
  define N'_pos where "N'_pos = N' \<inter> {C. Pos C \<in> N}"
  define N'_neg where "N'_neg = N' \<inter> {C. Neg C \<in> M}"
  have compactness_hypothesis:
    \<open>M'_pos \<union> M'_neg \<Turnstile> N'_pos \<union> N'_neg\<close>
    using inf.absorb_iff1 inf_sup_distrib1 M'_def N'_def M'_entails_N'
    unfolding M'_pos_def M'_neg_def N'_pos_def N'_neg_def
    by (smt (verit))
  have M'_pos_finite: \<open>finite M'_pos\<close> using M'_finite unfolding M'_pos_def by blast
  have \<open>finite M'_neg\<close> using M'_finite unfolding M'_neg_def by blast
  have \<open>finite N'_pos\<close> using N'_finite unfolding N'_pos_def by blast
  have \<open>finite N'_neg\<close> using N'_finite unfolding N'_neg_def by blast
  define M_fin where "M_fin = {Pos C |C. Pos C \<in> M \<and> C \<in> M'} \<union> {Neg C |C. Neg C \<in> M \<and> C \<in> N'}"
  then have fin_M_fin: \<open>finite M_fin\<close> using M'_finite N'_finite by auto
  have sub_M_fin: \<open>M_fin \<subseteq> M\<close>
    unfolding M_fin_def by blast
  define N_fin where "N_fin = {Pos C |C. Pos C \<in> N \<and> C \<in> N'} \<union> {Neg C |C. Neg C \<in> N \<and> C \<in> M'}"
  then have fin_N_fin: \<open>finite N_fin\<close> using N'_finite M'_finite by auto
  have sub_N_fin: \<open>N_fin \<subseteq> N\<close>
    unfolding N_fin_def by blast
  have \<open>{C. Pos C \<in> M_fin} = M'_pos\<close>
    unfolding M_fin_def M'_pos_def by blast
  moreover have \<open>{C. Neg C \<in> M_fin} = N'_neg\<close>
    unfolding M_fin_def N'_neg_def by blast
  moreover have \<open>{C. Pos C \<in> N_fin} = N'_pos\<close>
    unfolding N_fin_def N'_pos_def by blast
  moreover have \<open>{C. Neg C \<in> N_fin} = M'_neg\<close>
    unfolding N_fin_def M'_neg_def by blast
  ultimately have \<open>M_fin \<Turnstile>\<^sub>\<sim> N_fin\<close>
    unfolding entails_neg_def using compactness_hypothesis by force
  then show \<open>\<exists>M' N'. M' \<subseteq> M \<and> N' \<subseteq> N \<and> finite M' \<and> finite N' \<and> M' \<Turnstile>\<^sub>\<sim> N'\<close>
    using fin_M_fin fin_N_fin sub_M_fin sub_N_fin by auto
qed

interpretation neg_ext_cons_rel: consequence_relation "Pos bot" entails_neg
  using ext_cons_rel by simp
    
    (* Splitting report Lemma 1 *)
lemma pos_neg_entails_bot: \<open>{C} \<union> {neg C} \<Turnstile>\<^sub>\<sim> {Pos bot}\<close>
proof -
  have \<open>{C} \<union> {neg C} \<Turnstile>\<^sub>\<sim> {}\<close> unfolding entails_neg_def
    by (smt (verit, del_insts) Un_iff empty_subsetI entails_reflexive entails_subsets insertI1
        insert_is_Un insert_subset is_Pos.cases mem_Collect_eq neg.simps(1) neg.simps(2))
  then show ?thesis using neg_ext_cons_rel.entails_subsets by blast 
qed

end
  


locale sound_inference_system =
  inference_system Inf + sound_cons: consequence_relation bot entails_sound
  for
    Inf :: "'f inference set" and
    bot :: "'f" and
    entails_sound :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>s" 50)
  + assumes
    sound: "\<iota> \<in> Inf \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>s {concle_of \<iota>}"
    
   (* There are several options to represent sequences that I considered:
      - using everywhere a type \<open>nat \<Rightarrow> 'f set\<close> (pros: super simple, cons: maintenance heavy, i.e. any
    change must be propagated everywhere)
      - creating an abstract type as in Multiset.thy for the above type (pros: clean, cons: requires
    lifted definitions, i.e. more work)
      - restricting the lazy list codatatype used in RP and the saturation framework to only
    infinite lists (pros: closest to previous work, cons: propagate the restriction everywhere)
      - using one of the existing theory about infinite lists (which one?): HOL-library.Stream,
    lazy lists, infinite lists...

    Temporary conclusion: I'll try the last option with the Stream library.
    *)

no_notation IArray.sub (infixl "!!" 100)
  
definition is_derivation :: "('f set \<Rightarrow> 'f set \<Rightarrow> bool) \<Rightarrow> ('f set stream) \<Rightarrow> bool" where
  "is_derivation R Ns \<equiv> \<forall>i. R (Ns !! i) (Ns !! (Suc i))"
  
definition terminates :: "'f set stream \<Rightarrow> bool" where
  "terminates Ns \<equiv> \<exists>i. \<forall>j>i. Ns !! j = Ns !! i"

definition lim_inf :: "'f set stream \<Rightarrow> 'f set" where
  "lim_inf Ns = (\<Union>i. \<Inter>j \<in> {j. i \<le> j}. Ns !! j)"

abbreviation limit :: "'f set stream \<Rightarrow> 'f set" where "limit Ns \<equiv> lim_inf Ns"

definition lim_sup :: "'f set stream \<Rightarrow> 'f set" where
  "lim_sup Ns = (\<Inter>i. \<Union>j \<in> {j. i \<le> j}. Ns !! j)"

locale calculus = inference_system Inf + consequence_relation bot entails
  for
    bot :: "'f" and
    Inf :: \<open>'f inference set\<close> and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50)
  + fixes
    Red_I :: "'f set \<Rightarrow> 'f inference set" and
    Red_F :: "'f set \<Rightarrow> 'f set"
  assumes
    Red_I_to_Inf: "Red_I N \<subseteq> Inf" and
    Red_F_Bot: "N \<Turnstile> {bot} \<Longrightarrow> N - Red_F N \<Turnstile> {bot}" and (* /!\ check if this is ok *)
    Red_F_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'" and
    Red_I_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_I N \<subseteq> Red_I N'" and
    Red_F_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')" and
    Red_I_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_I N \<subseteq> Red_I (N - N')" and
    Red_I_of_Inf_to_N: "\<iota> \<in> Inf \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_I N"
begin

definition saturated :: "'f set \<Rightarrow> bool" where
  "saturated N \<longleftrightarrow> Inf_from N \<subseteq> Red_I N"
  
definition Red_I_strict :: "'f set \<Rightarrow> 'f inference set" where
  "Red_I_strict N = {\<iota>. \<iota> \<in> Red_I N \<or> (\<iota> \<in> Inf \<and> bot \<in> N)}"
  
definition Red_F_strict :: "'f set \<Rightarrow> 'f set" where
  "Red_F_strict N = {C. C \<in> Red_F N \<or> (bot \<in> N \<and> C \<noteq> bot)}"
  
(* This proof helped detect a lack of precision in rmk 3 (missing restriction in the hypotheses *)
lemma strict_calc_if_nobot:
  "\<forall>N. bot \<notin> Red_F N \<Longrightarrow> calculus bot Inf entails Red_I_strict Red_F_strict"
proof
  fix N
  show \<open>Red_I_strict N \<subseteq> Inf\<close> unfolding Red_I_strict_def using Red_I_to_Inf by blast
next
  fix N
  assume
    bot_notin: "\<forall>N. bot \<notin> Red_F N" and
    entails_bot: \<open>N \<Turnstile> {bot}\<close>
  show \<open>N - Red_F_strict N \<Turnstile> {bot}\<close>
  proof (cases "bot \<in> N")
    assume bot_in: "bot \<in> N"
    have \<open>bot \<notin> Red_F N\<close> using bot_notin by blast
    then have \<open>bot \<notin> Red_F_strict N\<close> unfolding Red_F_strict_def by blast 
    then have \<open>Red_F_strict N = UNIV - {bot}\<close>
      unfolding Red_F_strict_def using bot_in by blast
    then have \<open>N - Red_F_strict N = {bot}\<close> using bot_in by blast
    then show \<open>N - Red_F_strict N \<Turnstile> {bot}\<close> using entails_reflexive[of bot] by simp
  next
    assume \<open>bot \<notin> N\<close>
    then have \<open>Red_F_strict N = Red_F N\<close> unfolding Red_F_strict_def by blast
    then show \<open>N - Red_F_strict N \<Turnstile> {bot}\<close> using Red_F_Bot[OF entails_bot] by simp
  qed
next
  fix N N' :: "'f set"
  assume \<open>N \<subseteq> N'\<close>
  then show \<open>Red_F_strict N \<subseteq> Red_F_strict N'\<close>
    unfolding Red_F_strict_def using Red_F_of_subset by blast
next
  fix N N' :: "'f set"
  assume \<open>N \<subseteq> N'\<close>
  then show \<open>Red_I_strict N \<subseteq> Red_I_strict N'\<close>
    unfolding Red_I_strict_def using Red_I_of_subset by blast
next
  fix N' N
  assume
    bot_notin: "\<forall>N. bot \<notin> Red_F N" and
    subs_red: "N' \<subseteq> Red_F_strict N"
  have \<open>bot \<notin> Red_F_strict N\<close>
    using bot_notin unfolding Red_F_strict_def by blast
  then have nbot_in: \<open>bot \<notin> N'\<close> using subs_red by blast 
  show \<open>Red_F_strict N \<subseteq> Red_F_strict (N - N')\<close>
  proof (cases "bot \<in> N")
    case True
    then have bot_in: "bot \<in> N - N'" using nbot_in by blast
    then show ?thesis unfolding Red_F_strict_def using bot_notin by force
  next
    case False
    then have eq_red: "Red_F_strict N = Red_F N" unfolding Red_F_strict_def by simp
    then have "N' \<subseteq> Red_F N" using subs_red by simp
    then have "Red_F N \<subseteq> Red_F (N - N')" using Red_F_of_Red_F_subset by simp
    then show ?thesis using eq_red Red_F_strict_def by blast 
  qed
next
  fix N' N
  assume
    "\<forall>N. bot \<notin> Red_F N" and
    subs_red: "N' \<subseteq> Red_F_strict N"
  then have bot_notin: "bot \<notin> N'" unfolding Red_F_strict_def by blast 
  then show "Red_I_strict N \<subseteq> Red_I_strict (N - N')"
  proof (cases "bot \<in> N")
    case True
    then show ?thesis
      unfolding Red_I_strict_def using bot_notin Red_I_to_Inf by fastforce 
  next
    case False
    then show ?thesis
      using bot_notin Red_I_to_Inf subs_red Red_I_of_Red_F_subset 
      unfolding Red_I_strict_def Red_F_strict_def by simp
  qed
next
  fix \<iota> N
  assume "\<iota> \<in> Inf"
  then show "concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_I_strict N"
    unfolding Red_I_strict_def using Red_I_of_Inf_to_N Red_I_to_Inf by simp
qed

definition weakly_fair :: "'f set stream \<Rightarrow> bool" where
  "weakly_fair Ns \<equiv> Inf_from (lim_inf Ns) \<subseteq> (\<Union>i. (Red_I (Ns !! i)))"

abbreviation fair :: "'f set stream \<Rightarrow> bool" where "fair N \<equiv> weakly_fair N"

definition derive :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<rhd>" 50) where
  "M \<rhd> N \<equiv> (M - N \<subseteq> Red_F N)"

(* for reference, the definition used in the saturation framework *)
(* inductive "derive" :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<rhd>" 50) where
     derive: "M - N \<subseteq> Red_F N \<Longrightarrow> M \<rhd> N" *)

lemma derive_refl: "M \<rhd> M" unfolding derive_def by simp

lemma deriv_red_in: \<open>M \<rhd> N \<Longrightarrow> Red_F M \<subseteq> N \<union> Red_F N\<close>
proof -
  fix M N
  assume deriv: \<open>M \<rhd> N\<close>
  then have \<open>M \<subseteq> N \<union> Red_F N\<close>
    unfolding derive_def by blast 
  then have red_m_in: \<open>Red_F M \<subseteq> Red_F (N \<union> Red_F N)\<close>
    using Red_F_of_subset by blast 
  have \<open>Red_F (N \<union> Red_F N) \<subseteq> Red_F (N \<union> Red_F N - (Red_F N - N))\<close>
    using Red_F_of_Red_F_subset[of "Red_F N - N" "N \<union> Red_F N"]
      Red_F_of_subset[of "N" "N \<union> Red_F N"] by fast
  then have \<open>Red_F (N \<union> Red_F N) \<subseteq> Red_F N\<close>
    by (metis Diff_subset_conv Red_F_of_subset Un_Diff_cancel lfp.leq_trans subset_refl sup.commute)
  then show \<open>Red_F M \<subseteq> N \<union> Red_F N\<close> using red_m_in by blast
qed

lemma derive_trans: "M \<rhd> N \<Longrightarrow> N \<rhd> N' \<Longrightarrow> M \<rhd> N'" 
  using deriv_red_in by (smt Diff_subset_conv derive_def subset_trans sup.absorb_iff2)

end
  
locale sound_calculus = sound_inference_system Inf bot entails_sound +
  consequence_relation bot entails
  for
    bot :: "'f" and
    Inf :: \<open>'f inference set\<close> and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) and
    entails_sound :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>s" 50)
    + fixes
    Red_I :: "'f set \<Rightarrow> 'f inference set" and
    Red_F :: "'f set \<Rightarrow> 'f set"
    assumes
      Red_I_to_Inf: "Red_I N \<subseteq> Inf" and
      Red_F_Bot: "N \<Turnstile> {bot} \<Longrightarrow> N - Red_F N \<Turnstile> {bot}" and (* /!\ check if this is ok *)
      Red_F_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'" and
      Red_I_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_I N \<subseteq> Red_I N'" and
      Red_F_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')" and
      Red_I_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_I N \<subseteq> Red_I (N - N')" and
      Red_I_of_Inf_to_N: "\<iota> \<in> Inf \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_I N"
begin

sublocale calculus bot Inf entails
  by (simp add: Preliminaries_With_Zorn.calculus.intro Preliminaries_With_Zorn.calculus_axioms.intro Red_F_Bot
    Red_F_of_Red_F_subset Red_F_of_subset Red_I_of_Inf_to_N Red_I_of_Red_F_subset Red_I_of_subset
    Red_I_to_Inf consequence_relation_axioms)
end
      
locale statically_complete_calculus = calculus +
  assumes statically_complete: "saturated N \<Longrightarrow> N \<Turnstile> {bot} \<Longrightarrow> bot \<in> N"
begin

lemma inf_from_subs: "M \<subseteq> N \<Longrightarrow> Inf_from M \<subseteq> Inf_from N"
  unfolding Inf_from_def by blast
    
    (* Splitting report Lemma 3 *)
lemma nobot_in_Red: \<open>bot \<notin> Red_F N\<close>
proof -
  have \<open>UNIV \<Turnstile> {bot}\<close>
    using entails_reflexive[of bot] entails_subsets[of "{bot}" UNIV "{bot}" "{bot}"] by fast
  then have non_red_entails_bot: \<open>UNIV - (Red_F UNIV) \<Turnstile> {bot}\<close> using Red_F_Bot[of UNIV] by simp
  have \<open>Inf_from UNIV \<subseteq> Red_I UNIV\<close>
    unfolding Inf_from_def using Red_I_of_Inf_to_N[of _ UNIV] by blast
  then have sat_non_red: \<open>saturated (UNIV - Red_F UNIV)\<close>
    unfolding saturated_def Inf_from_def using Red_I_of_Red_F_subset[of "Red_F UNIV" UNIV] by blast 
  have \<open>bot \<notin> Red_F UNIV\<close> 
    using statically_complete[OF sat_non_red non_red_entails_bot] by fast
  then show ?thesis using Red_F_of_subset[of _ UNIV] by auto
qed
  
  (* Splitting report Remark 4 *)
interpretation strict_calculus:
  statically_complete_calculus bot Inf entails Red_I_strict Red_F_strict
proof -
  interpret strict_calc: calculus bot Inf entails Red_I_strict Red_F_strict
  using strict_calc_if_nobot nobot_in_Red by blast 
    (* next property is not needed for the proof, but it is one of the claims from Rmk 3
    that must be verified *)
  have \<open>saturated N \<Longrightarrow> strict_calc.saturated N\<close>
    unfolding saturated_def strict_calc.saturated_def Red_I_strict_def by blast
  have \<open>strict_calc.saturated N \<Longrightarrow> N \<Turnstile> {bot} \<Longrightarrow> bot \<in> N\<close> for N
  proof -
    assume
      strict_sat: "strict_calc.saturated N" and
      entails_bot: "N \<Turnstile> {bot}"
    have \<open>bot \<notin> N \<Longrightarrow> Red_I_strict N = Red_I N\<close> unfolding Red_I_strict_def by simp
    then have \<open>bot \<notin> N \<Longrightarrow> saturated N\<close>
      unfolding saturated_def using strict_sat by (simp add: strict_calc.saturated_def) 
    then have \<open>bot \<notin> N \<Longrightarrow> bot \<in> N\<close>
      using statically_complete[OF _ entails_bot] by simp
    then show \<open>bot \<in> N\<close> by auto 
  qed
  then show \<open>statically_complete_calculus bot Inf entails Red_I_strict Red_F_strict\<close>
    unfolding statically_complete_calculus_def statically_complete_calculus_axioms_def
    using strict_calc.calculus_axioms by blast
qed

end

locale dynamically_complete_calculus = calculus +
  assumes dynamically_complete:
    \<open>is_derivation (\<rhd>) Ns \<Longrightarrow> fair Ns \<Longrightarrow> shd Ns \<Turnstile> {bot} \<Longrightarrow> \<exists>i. bot \<in> Ns !! i\<close>

    (* First attempt at formalizing sect. 2.3 *)
    (* below, I force 'v to be countable, but not infinite, alternative, enforce bijection with nat
    in the first locale where it is used? *)

    (* records are definitely overkill for this *)
(* record ('f, 'v::countable) AF =
 *   F :: 'f
 *     A :: "'v neg set" *)
    
    (* discussions on this datatype allowed to detect a spurious assumption: 'v doesn't need to be
    infinite*)
    (* TODO: should "countable" be added as a requirement of the AF_calculus locale? *)
datatype ('f, 'v::countable) AF = Pair (F_of: "'f") (A_of: "'v sign fset")

definition is_interpretation :: "'v sign set \<Rightarrow> bool" where
  \<open>is_interpretation J = (\<forall>v1\<in>J. (\<forall>v2\<in>J. (to_V v1 = to_V v2 \<longrightarrow> v1 = v2)))\<close>
  
  (* TODO: find a shorter name for this type (?) *)
typedef 'v propositional_interpretation = "{J :: 'v sign set. is_interpretation J}"
proof
  show \<open>{} \<in> {J. is_interpretation J}\<close> unfolding is_interpretation_def by blast 
qed
  
  find_theorems name: Abs name: propositional_interpretation

abbreviation "interp_of \<equiv> Abs_propositional_interpretation"
abbreviation "strip \<equiv> Rep_propositional_interpretation"

context
begin
  setup_lifting type_definition_propositional_interpretation

  lift_definition belong_to :: "'v sign \<Rightarrow> 'v propositional_interpretation \<Rightarrow> bool" (infix "\<in>\<^sub>J" 90)
    is "(\<in>)::('v sign \<Rightarrow> 'v sign set \<Rightarrow> bool)" .
end

definition total :: "'v propositional_interpretation \<Rightarrow> bool" where
  \<open>total J \<equiv> (\<forall>v. (\<exists>v\<^sub>J. v\<^sub>J \<in>\<^sub>J J \<and> to_V v\<^sub>J = v))\<close>
  
typedef 'v total_interpretation = "{J :: 'v propositional_interpretation. total J}"
proof
  show \<open>interp_of (Pos ` (UNIV :: 'v set)) \<in> {J. total J}\<close>
    unfolding total_def   
  proof 
    show "\<forall>v. \<exists>v\<^sub>J. v\<^sub>J \<in>\<^sub>J interp_of (range Pos) \<and> to_V v\<^sub>J = v"
    proof
      fix v
      have "Pos v \<in>\<^sub>J interp_of (range Pos) \<and> to_V (Pos v) = v"
        by (simp add: Abs_propositional_interpretation_inverse belong_to.rep_eq is_interpretation_def)
      then show "\<exists>v\<^sub>J. v\<^sub>J \<in>\<^sub>J interp_of (range Pos) \<and> to_V v\<^sub>J = v" by blast
    qed
  qed
qed

abbreviation "total_interp_of \<equiv> (\<lambda>x. Abs_total_interpretation (interp_of x))"
abbreviation "total_strip \<equiv> (\<lambda>x. strip (Rep_total_interpretation x))"

lemma [simp]: \<open>(neg a \<notin> total_strip J) = (a \<in> total_strip J)\<close>
proof
  assume neg_a_notin: \<open>neg a \<notin> total_strip J\<close>
  have \<open>\<exists>b. to_V a = to_V b \<and> b \<in> total_strip J\<close>
    by (metis Rep_total_interpretation belong_to.rep_eq mem_Collect_eq total_def)
  then show \<open>a \<in> total_strip J\<close>
    using neg_a_notin by (metis neg.simps to_V.elims)
next
  assume a_in: \<open>a \<in> total_strip J\<close>
  then have \<open>\<exists>b. to_V a = to_V b \<and> b \<notin> total_strip J\<close>
    by (metis Rep_propositional_interpretation is_interpretation_def mem_Collect_eq sign.simps(4)
        to_V.simps)
  then show \<open>neg a \<notin> total_strip J\<close>
    using a_in by (metis neg.simps to_V.elims)
qed

lemma [simp]: \<open>(neg a \<in> total_strip J) = (a \<notin> total_strip J)\<close>
proof
  assume neg_a_notin: \<open>neg a \<in> total_strip J\<close>
  have \<open>\<exists>b. to_V a = to_V b \<and> b \<notin> total_strip J\<close>
   by (metis Rep_propositional_interpretation is_interpretation_def mem_Collect_eq sign.simps(4)
        to_V.simps)
  then show \<open>a \<notin> total_strip J\<close>
    using neg_a_notin by (metis neg.simps to_V.elims)
next
  assume a_in: \<open>a \<notin> total_strip J\<close>
  then have \<open>\<exists>b. to_V a = to_V b \<and> b \<in> total_strip J\<close>
    by (metis Rep_total_interpretation belong_to.rep_eq mem_Collect_eq total_def)
  then show \<open>neg a \<in> total_strip J\<close>
    using a_in by (metis neg.simps to_V.elims)
qed

context
begin
  (* TODO : seems the command below fails. What is its impact? *)
  setup_lifting type_definition_total_interpretation

  lift_definition belong_to_total :: "'v sign \<Rightarrow> 'v total_interpretation \<Rightarrow> bool" (infix "\<in>\<^sub>t" 90)
    is "(\<in>\<^sub>J)::('v sign \<Rightarrow> 'v propositional_interpretation \<Rightarrow> bool)" .
end
  (* TODO? If propositional_interpretation is never used, directly define total_interpretation from
  \<t>erm \<open>'v neg set\<close> *)

lemma [simp]: \<open>a \<in>\<^sub>t J \<longleftrightarrow> a \<in> total_strip J\<close>
  unfolding belong_to_total_def belong_to_def by simp

lemma neg_prop_interp: \<open>(v::'v sign) \<in>\<^sub>J J \<Longrightarrow> \<not> ((neg v) \<in>\<^sub>J J)\<close>
proof transfer
  fix v J
  assume
    j_is: \<open>is_interpretation (J:: 'v sign set)\<close> and
    v_in: \<open>v \<in> J\<close>
  then show \<open>\<not> (neg v) \<in> J\<close>
  proof (cases v)
    case (Pos C)
    then show ?thesis
      using is_Pos.simps
      by (metis is_interpretation_def j_is neg.simps(1) to_V.simps v_in)
  next
    case (Neg C)
    then show ?thesis
      using j_is v_in
      using is_interpretation_def by fastforce
  qed
qed

lemma neg_total_interp: \<open>(v::'v sign) \<in>\<^sub>t J \<Longrightarrow> \<not> ((neg v) \<in>\<^sub>t J)\<close>
proof transfer
  fix v J
  assume v_in: \<open>v \<in>\<^sub>J (J :: 'v propositional_interpretation)\<close>
  show \<open>\<not> neg v \<in>\<^sub>J J\<close>
    using neg_prop_interp[OF v_in] by simp
qed

definition to_AF :: "'f \<Rightarrow> ('f, 'v::countable) AF" where
  \<open>to_AF C = Pair C {||}\<close>

definition Neg_set :: "'v sign set \<Rightarrow> 'v sign set" ("\<sim>_" 55) where
  \<open>\<sim>V \<equiv> {neg v |v. v \<in> V}\<close>

definition F_of_Inf :: "(('f, 'v::countable) AF) inference \<Rightarrow> 'f inference" where
  \<open>F_of_Inf \<iota>\<^sub>A\<^sub>F = (Infer (map F_of (prems_of \<iota>\<^sub>A\<^sub>F)) (F_of (concl_of \<iota>\<^sub>A\<^sub>F)))\<close>
  
(* locale propositional_interpretations =
 *   fixes
 *     \<J> :: "'v::countable neg set set"
 *   assumes
 *     all_interp: "J \<in> \<J> \<Longrightarrow> is_interpretation J" and
  *     all_in_J: "is_interpretation J \<Longrightarrow> J \<in> \<J>" *)


locale AF_calculus = sound_calculus bot Inf entails entails_sound Red_I Red_F
  (* + propositional_interpretations \<J>*)
  for
    bot :: "'f" and
    Inf :: \<open>'f inference set\<close> and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) and
    entails_sound :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>s" 50) and
    Red_I :: "'f set \<Rightarrow> 'f inference set" and
    Red_F :: "'f set \<Rightarrow> 'f set"
  + fixes
    V:: "'v::countable itself" and
    (* \<J> :: "'v::countable neg set set" and *)
    fml :: "'v \<Rightarrow> 'f"
    assumes
      entails_sound_compact: \<open>M \<Turnstile>s N \<Longrightarrow> (\<exists>M'\<subseteq>M. (\<exists>N'\<subseteq>N. finite M' \<and> finite N' \<and> M' \<Turnstile>s N'))\<close>
    (*  j_is: \<open>\<J> = {J. is_interpretation J}\<close>*)
begin
  
  (* various attempts at representing the "enabled" concept *)
(* definition enabled0 :: "('f, 'v) AF \<Rightarrow> 'v neg set \<Rightarrow> bool" where
 *   \<open>enabled0 C J = (J \<in> \<J> \<and> ((A_of C) \<subseteq> J \<or> (F_of C = bot \<and> (\<sim> (A_of C)) \<inter> J = {})))\<close> *)

  (* J must be an interpretation, but this could also be verified outside of the definitions *)
(* inductive "enabled" :: "('f, 'v) AF \<Rightarrow> 'v neg set \<Rightarrow> bool" where
 *   cond1: "J \<in> \<J> \<Longrightarrow> (A_of C) \<subseteq> J \<Longrightarrow> enabled C J" |
  *   cond2: "J \<in> \<J> \<Longrightarrow> (F_of C = bot \<and> (\<sim> (A_of C)) \<inter> J = {}) \<Longrightarrow> enabled C J" *)
  
(* inductive "enabled" :: "('f, 'v) AF \<Rightarrow> 'v total_interpretation \<Rightarrow> bool" where
 *   cond1: "(A_of C) \<subseteq> (total_strip J) \<Longrightarrow> enabled C J" |
  *   cond2: "(F_of C = bot \<and> (\<sim> (A_of C)) \<inter> (total_strip J) = {}) \<Longrightarrow> enabled C J" *)

definition \<iota>F_of :: "('f, 'v) AF inference \<Rightarrow> 'f inference" where
  \<open>\<iota>F_of \<iota> = Infer (List.map F_of (prems_of \<iota>)) (F_of (concl_of \<iota>))\<close>
  
definition propositional_projection :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set" ("proj\<^sub>\<bottom>") where
  \<open>proj\<^sub>\<bottom> \<N> = {\<C>. \<C> \<in> \<N> \<and> F_of \<C> = bot}\<close>

lemma prop_proj_in: \<open>proj\<^sub>\<bottom> \<N> \<subseteq> \<N>\<close>
  unfolding propositional_projection_def by blast

definition enabled :: "('f, 'v) AF \<Rightarrow> 'v total_interpretation \<Rightarrow> bool" where
  "enabled \<C> J \<equiv> fset (A_of \<C>) \<subseteq> (total_strip J)"

definition enabled_set :: "('f, 'v) AF set \<Rightarrow> 'v total_interpretation \<Rightarrow> bool" where
  \<open>enabled_set \<N> J = (\<forall>\<C>\<in>\<N>. enabled \<C> J)\<close>

definition enabled_inf :: "('f, 'v) AF inference \<Rightarrow> 'v total_interpretation \<Rightarrow> bool" where
  \<open>enabled_inf \<iota> J = (\<forall>\<C>\<in> set (prems_of \<iota>). enabled \<C> J)\<close>
  
definition enabled_projection :: "('f, 'v) AF set \<Rightarrow> 'v total_interpretation \<Rightarrow> 'f set"
  (infix "proj\<^sub>J" 60)  where
  \<open>\<N> proj\<^sub>J J = {F_of \<C> |\<C>. \<C> \<in> \<N> \<and> enabled \<C> J}\<close>

definition enabled_projection_Inf :: "('f, 'v) AF inference set \<Rightarrow> 'v total_interpretation \<Rightarrow>
  'f inference set" (infix "\<iota>proj\<^sub>J" 60) where
  \<open>I \<iota>proj\<^sub>J J = {\<iota>F_of \<iota> | \<iota>. \<iota> \<in> I \<and> enabled_inf \<iota> J}\<close>

fun fml_ext :: "'v sign \<Rightarrow> 'f sign" where
  "fml_ext (Pos v) = Pos (fml v)" |
  "fml_ext (Neg v) = Neg (fml v)"

lemma fml_ext_preserves_sign: "is_Pos v \<equiv> is_Pos (fml_ext v)"
  by (induct v, auto)

lemma [simp]: \<open>to_V (fml_ext v) = fml (to_V v)\<close>
  by (induct v, auto) 

lemma fml_ext_preserves_val: \<open>to_V v1 = to_V v2 \<Longrightarrow> to_V (fml_ext v1) = to_V (fml_ext v2)\<close>
  by simp
 
definition sound_consistent :: "'v total_interpretation \<Rightarrow> bool" where
  \<open>sound_consistent J \<equiv> \<not> (sound_cons.entails_neg (fml_ext ` (total_strip J)) {Pos bot})\<close>
  
  (* most probably overkill *)
(* abbreviation F_of_set :: "('f, 'v) AF set \<Rightarrow> 'f set" where
  \<open>F_of_set N \<equiv> F_of ` N\<close> *)





(* TODO: try alternative def that makes use of prop semantic from AFP to ease use of compactness *)
definition propositional_model :: "'v total_interpretation \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool"
  (infix "\<Turnstile>\<^sub>p" 50) where
  \<open>J \<Turnstile>\<^sub>p \<N> \<equiv> bot \<notin> ((proj\<^sub>\<bottom> \<N>) proj\<^sub>J J)\<close>

lemma \<open>J \<Turnstile>\<^sub>p {}\<close> unfolding propositional_model_def enabled_projection_def propositional_projection_def by blast
 
definition propositional_model2 :: "'v total_interpretation \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool"
  (infix "\<Turnstile>\<^sub>p2" 50) where
  \<open>J \<Turnstile>\<^sub>p2 \<N> \<equiv> ({} = ((proj\<^sub>\<bottom> \<N>) proj\<^sub>J J))\<close>


fun sign_to_atomic_formula :: "'v sign \<Rightarrow> 'v formula" where
  \<open>sign_to_atomic_formula (Pos v) = Atom v\<close> |
  \<open>sign_to_atomic_formula (Neg v) = Not (Atom v)\<close>

definition sign_set_to_formula_set :: "'v sign set \<Rightarrow> 'v formula set" where
  \<open>sign_set_to_formula_set A = sign_to_atomic_formula ` A\<close>

lemma form_shape_sign_set: \<open>\<forall>f\<in>sign_set_to_formula_set A. \<exists>v. f = Atom v \<or> f = Not (Atom v)\<close>
  unfolding sign_set_to_formula_set_def
  by (metis image_iff sign_to_atomic_formula.elims)

definition AF_to_formula_set :: "('f, 'v) AF \<Rightarrow> 'v formula set" where
  (* /!\ this formula set is to be understood as a disjunction *)
  \<open>AF_to_formula_set \<C> = sign_set_to_formula_set (neg ` fset (A_of \<C>))\<close>

(* to move to Fset theory? *)
definition list_of_fset :: "'a fset \<Rightarrow> 'a list" where
  \<open>list_of_fset A = (SOME l. fset_of_list l = A)\<close>

definition AF_to_formula :: "('f, 'v) AF \<Rightarrow> 'v formula" where
  \<open>AF_to_formula \<C> = BigOr (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>))))\<close>

lemma form_shape_AF: \<open>\<forall>f\<in>AF_to_formula_set \<C>. \<exists>v. f = Atom v \<or> f = Not (Atom v)\<close>
  using form_shape_sign_set unfolding AF_to_formula_set_def by simp

definition AF_proj_to_formula_set_set :: "('f, 'v) AF set \<Rightarrow> 'v formula set set" where
  (* /!\ formula set set represents here a conjuction of disjunctions *)
  \<open>AF_proj_to_formula_set_set \<N> = AF_to_formula_set ` (proj\<^sub>\<bottom> \<N>)\<close>

definition AF_proj_to_formula_set :: "('f, 'v) AF set \<Rightarrow> 'v formula set" where
  \<open>AF_proj_to_formula_set \<N> = AF_to_formula ` (proj\<^sub>\<bottom> \<N>)\<close>

definition AF_assertions_to_formula :: "('f, 'v) AF \<Rightarrow> 'v formula" where
  \<open>AF_assertions_to_formula \<C> = BigAnd (map sign_to_atomic_formula (list_of_fset (A_of \<C>)))\<close>

definition AF_assertions_to_formula_set :: "('f, 'v) AF set \<Rightarrow> 'v formula set" where
  \<open>AF_assertions_to_formula_set \<N> = AF_assertions_to_formula ` \<N>\<close>

lemma F_to_\<C>_set: \<open>\<forall>F\<in>AF_proj_to_formula_set_set \<N>. \<exists>\<C>\<in>proj\<^sub>\<bottom> \<N>. F =
  sign_to_atomic_formula ` neg ` fset (A_of \<C>)\<close>
  unfolding AF_proj_to_formula_set_set_def AF_to_formula_set_def sign_set_to_formula_set_def
  by auto
(* TODO: show to Mathias: sledgehammer suggests "by blast" (for all provers) but this fails *)

lemma F_to_\<C>: \<open>\<forall>F\<in>AF_proj_to_formula_set \<N>. \<exists>\<C>\<in>proj\<^sub>\<bottom> \<N>. F =
   BigOr (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>))))\<close>
  unfolding AF_proj_to_formula_set_def AF_to_formula_def by auto

lemma \<C>_to_F_set: \<open>\<forall>\<C>\<in>proj\<^sub>\<bottom> \<N>. \<exists>F\<in>AF_proj_to_formula_set_set \<N>. F =
  sign_to_atomic_formula ` neg ` fset (A_of \<C>)\<close>
  unfolding AF_proj_to_formula_set_set_def AF_to_formula_set_def sign_set_to_formula_set_def
  by auto

lemma \<C>_to_F: \<open>\<forall>\<C>\<in>proj\<^sub>\<bottom> \<N>. \<exists>F\<in>AF_proj_to_formula_set \<N>. F =
  BigOr (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>))))\<close>
  unfolding AF_proj_to_formula_set_def AF_to_formula_def by auto

lemma form_shape_proj: \<open>\<forall>f\<in>\<Union> (AF_proj_to_formula_set_set \<N>). \<exists>v. f = Atom v \<or> f = Not (Atom v)\<close>
  using form_shape_AF unfolding AF_proj_to_formula_set_set_def by simp

definition to_valuation :: "'v total_interpretation \<Rightarrow> 'v valuation" where
  \<open>to_valuation J = (\<lambda>a. Pos a \<in>\<^sub>t J)\<close>

find_theorems strip 

lemma val_strip_pos: \<open>to_valuation J a \<equiv> Pos a \<in> total_strip J\<close>
  unfolding to_valuation_def belong_to_total_def belong_to_def by simp

lemma val_strip_neg: \<open>(\<not> to_valuation J a) = (Neg a \<in> total_strip J)\<close>
proof -
  have \<open>(\<not> to_valuation J a) = (\<not> Pos a \<in> total_strip J)\<close>
    using val_strip_pos by simp
  also have \<open>(\<not> Pos a \<in> total_strip J) = (Neg a \<in> total_strip J)\<close>
  proof
    fix a J
    assume not_pos: \<open>Pos (a::'v) \<notin> total_strip J\<close>
    have \<open>is_interpretation (total_strip J)\<close>
      using Rep_propositional_interpretation by blast 
    then show \<open>Neg a \<in> total_strip J\<close> 
      unfolding is_interpretation_def using total_def not_pos
      by (metis Rep_total_interpretation belong_to.rep_eq mem_Collect_eq to_V.elims)
  next
    assume neg: \<open>Neg a \<in> total_strip J\<close>
    have \<open>is_interpretation (total_strip J)\<close>
      using Rep_propositional_interpretation by blast
    then show \<open>Pos a \<notin> total_strip J\<close>
      unfolding is_interpretation_def using neg
    by (metis sign.distinct(1) to_V.simps(1) to_V.simps(2))
  qed
  finally show \<open>(\<not> to_valuation J a) = (Neg a \<in> total_strip J)\<close> .
qed

lemma equiv_prop_entails: \<open>(J \<Turnstile>\<^sub>p \<N>) \<longleftrightarrow> (J \<Turnstile>\<^sub>p2 \<N>)\<close>
  unfolding propositional_model_def propositional_model2_def propositional_projection_def
    enabled_projection_def
  by blast

(* The interest of this first semantic characterization is that it is computable, but it is not
   convenient to apply the compactness results *)
lemma equiv_prop_entail2_sema:
  \<open>(J \<Turnstile>\<^sub>p2 \<N>) \<longleftrightarrow> (\<forall>F\<in>AF_proj_to_formula_set_set \<N>. \<exists>f\<in>F. formula_semantics (to_valuation J) f)\<close>
  unfolding propositional_model2_def enabled_projection_def enabled_def
proof
  assume empty_proj: \<open>{} = {F_of \<C> |\<C>. \<C> \<in> proj\<^sub>\<bottom> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
  then have \<open>\<forall>\<C>\<in>proj\<^sub>\<bottom> \<N>. \<exists>v\<in>fset (A_of \<C>). neg v \<in> total_strip J\<close> 
    by (smt (verit, ccfv_SIG) empty_iff mem_Collect_eq neg.elims subsetI
        val_strip_neg val_strip_pos)
  show \<open>\<forall>F\<in>AF_proj_to_formula_set_set \<N>. \<exists>f\<in>F. formula_semantics (to_valuation J) f\<close>
  proof
    fix F
    assume F_in: \<open>F \<in> AF_proj_to_formula_set_set \<N>\<close>
    then obtain \<C> where \<open>\<C> \<in> proj\<^sub>\<bottom> \<N>\<close> and F_from_\<C>: \<open>F = sign_to_atomic_formula ` neg ` fset (A_of \<C>)\<close>
      using F_to_\<C>_set by meson
    then have \<open>\<exists>v\<in>fset (A_of \<C>). v \<notin> total_strip J\<close>
      using empty_proj by blast
    then obtain v where v_in: \<open>v \<in> fset (A_of \<C>)\<close> and v_notin: \<open>v \<notin> total_strip J\<close> by auto
    define f where \<open>f = sign_to_atomic_formula (neg v)\<close>
    then have \<open>formula_semantics (to_valuation J) f\<close>
      using v_notin
      by (smt (z3) belong_to.rep_eq belong_to_total.rep_eq formula_semantics.simps neg.elims
          sign_to_atomic_formula.simps to_valuation_def val_strip_neg)
    moreover have \<open>f \<in> F\<close>
      using F_from_\<C> v_in f_def by blast
    ultimately show \<open>\<exists>f\<in>F. formula_semantics (to_valuation J) f\<close> by auto
  qed
next
  assume F_sat: \<open>\<forall>F\<in>AF_proj_to_formula_set_set \<N>. \<exists>f\<in>F. formula_semantics (to_valuation J) f\<close>
  have \<open>\<forall>\<C>\<in>proj\<^sub>\<bottom> \<N>. \<exists>v\<in>fset (A_of \<C>). neg v \<in> total_strip J\<close>
  proof
    fix \<C>
    assume \<open>\<C> \<in> proj\<^sub>\<bottom> \<N>\<close>
    then obtain F where \<open>F \<in> AF_proj_to_formula_set_set \<N>\<close> and
      F_from_\<C>: \<open>F = sign_to_atomic_formula ` neg ` fset (A_of \<C>)\<close>
      using \<C>_to_F_set by blast
    then have \<open>\<exists>f\<in>F. formula_semantics (to_valuation J) f\<close>
      using F_sat by blast
    then obtain f where f_in: \<open>f \<in> F\<close> and sat_f: \<open>formula_semantics (to_valuation J) f\<close>
      by blast
    then obtain v where v_is: \<open>f = sign_to_atomic_formula (neg v)\<close> and v_in: \<open>v \<in> fset (A_of \<C>)\<close>
      using F_from_\<C> by blast
    then have \<open>neg v \<in> total_strip J\<close>
      using sat_f unfolding to_valuation_def
      by (smt (z3) belong_to.rep_eq belong_to_total.rep_eq formula_semantics.simps sign.exhaust
          sign_to_atomic_formula.simps val_strip_neg val_strip_pos)
    then show \<open>\<exists>v\<in>fset (A_of \<C>). neg v \<in> total_strip J\<close>
      using v_in by auto
  qed
  then show \<open>{} = {F_of \<C> |\<C>. \<C> \<in> proj\<^sub>\<bottom> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
    by (smt (verit, ccfv_threshold) empty_Collect_eq is_Pos.cases neg.simps(1) neg.simps(2) subsetD
        val_strip_neg val_strip_pos)
qed

lemma fset_map2: \<open>v \<in> fset A \<Longrightarrow> g (f v) \<in> set (map g (map f (list_of_fset A)))\<close>
proof -
  assume \<open>v \<in> fset A\<close>
  then show \<open>g (f v) \<in> set (map g (map f (list_of_fset A)))\<close>
    unfolding list_of_fset_def
    by (smt (verit, ccfv_SIG) exists_fset_of_list fset_of_list.rep_eq imageI list.set_map someI_ex)
qed

(* this characterization can be used to apply the compactness from Michaelis & Nipkow but it uses
   something that can't be computed (SOME) *)
lemma equiv_prop_entail2_sema2:
  \<open>(J \<Turnstile>\<^sub>p2 \<N>) \<longleftrightarrow> (\<forall>F\<in>AF_proj_to_formula_set \<N>. formula_semantics (to_valuation J) F)\<close>
  unfolding propositional_model2_def enabled_projection_def enabled_def
proof
  assume empty_proj: \<open>{} = {F_of \<C> |\<C>. \<C> \<in> proj\<^sub>\<bottom> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
  show \<open>\<forall>F\<in>AF_proj_to_formula_set \<N>. formula_semantics (to_valuation J) F\<close>
  proof
    fix F
    assume F_in: \<open>F \<in> AF_proj_to_formula_set \<N>\<close>
    then obtain \<C> where \<open>\<C> \<in> proj\<^sub>\<bottom> \<N>\<close> and 
      F_from_\<C>: \<open>F = BigOr (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>))))\<close>
      using F_to_\<C> by meson
    then have \<open>\<exists>v\<in>fset (A_of \<C>). v \<notin> total_strip J\<close>
      using empty_proj by blast
    then obtain v where v_in: \<open>v \<in> fset (A_of \<C>)\<close> and v_notin: \<open>v \<notin> total_strip J\<close> by auto
    define f where \<open>f = sign_to_atomic_formula (neg v)\<close>
    then have \<open>formula_semantics (to_valuation J) f\<close>
      using v_notin
      by (smt (z3) belong_to.rep_eq belong_to_total.rep_eq formula_semantics.simps neg.elims
          sign_to_atomic_formula.simps to_valuation_def val_strip_neg)
    moreover have \<open>f \<in> set (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>))))\<close>
      unfolding f_def using fset_map2[OF v_in, of sign_to_atomic_formula neg] .
    ultimately have \<open>\<exists>f\<in>set (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>)))).
     formula_semantics (to_valuation J) f\<close>
      by blast
    then show \<open>formula_semantics (to_valuation J) F\<close>
      using BigOr_semantics[of "to_valuation J"
          "map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>)))"] F_from_\<C>
      by meson
    qed
next
  assume F_sat: \<open>\<forall>F\<in>AF_proj_to_formula_set \<N>. formula_semantics (to_valuation J) F\<close>
  have \<open>\<forall>\<C>\<in>proj\<^sub>\<bottom> \<N>. \<exists>v\<in>fset (A_of \<C>). neg v \<in> total_strip J\<close>
  proof
    fix \<C>
    assume \<C>_in: \<open>\<C> \<in> proj\<^sub>\<bottom> \<N>\<close>
    define F where \<open>F = AF_to_formula \<C>\<close>
    then have \<open>F \<in> AF_proj_to_formula_set \<N>\<close>
      unfolding AF_proj_to_formula_set_def using \<C>_in by blast
    then have \<open>formula_semantics (to_valuation J) F\<close> using F_sat by blast
    then have \<open>\<exists>f\<in>set (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>)))).
      formula_semantics (to_valuation J) f\<close>
      using BigOr_semantics[of "to_valuation J"] unfolding F_def AF_to_formula_def by simp
    then obtain f where 
      f_in: \<open>f \<in> set (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>))))\<close>
      and val_f: \<open>formula_semantics (to_valuation J) f\<close> by blast
    obtain v where v_in: \<open>v \<in> fset (A_of \<C>)\<close> and f_is: \<open>f = sign_to_atomic_formula (neg v)\<close>
      using f_in unfolding list_of_fset_def
      by (smt (z3) exists_fset_of_list fset_of_list.rep_eq image_iff list.set_map someI)
    have \<open>neg v \<in> total_strip J\<close>
      using f_is val_f unfolding to_valuation_def
      by (metis (mono_tags, lifting) belong_to.rep_eq belong_to_total.rep_eq 
          formula_semantics.simps(1) formula_semantics.simps(3) sign_to_atomic_formula.cases
          sign_to_atomic_formula.simps(1) sign_to_atomic_formula.simps(2) val_f val_strip_neg)
    then show \<open>\<exists>v\<in>fset (A_of \<C>). neg v \<in> total_strip J\<close>
      using v_in by blast
  qed
  then show \<open>{} = {F_of \<C> |\<C>. \<C> \<in> proj\<^sub>\<bottom> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
    by (smt (verit, ccfv_threshold) empty_Collect_eq is_Pos.cases neg.simps(1) neg.simps(2) subsetD
        val_strip_neg val_strip_pos)
qed

lemma equiv_prop_entail_sema:
  \<open>(J \<Turnstile>\<^sub>p \<N>) \<longleftrightarrow> (\<forall>F\<in>AF_proj_to_formula_set_set \<N>. \<exists>f\<in>F. formula_semantics (to_valuation J) f)\<close>
  using equiv_prop_entails equiv_prop_entail2_sema by presburger

definition propositional_model3 :: "'v total_interpretation \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool"
  (infix "\<Turnstile>\<^sub>p3" 50) where
  \<open>J \<Turnstile>\<^sub>p3 \<N> \<equiv> (\<forall>F\<in>AF_proj_to_formula_set_set \<N>. \<exists>f\<in>F. formula_semantics (to_valuation J) f)\<close>

lemma \<open>f ` fset A = set (map f (list_of_fset A))\<close>
proof
  show \<open>f ` fset A \<subseteq> set (map f (list_of_fset A))\<close>
  proof
    fix v
    assume \<open>v \<in> f ` fset A\<close>
    then obtain a where "a |\<in>| A" "f a = v"
      by (metis image_iff notin_fset)
    then show \<open>v \<in> set (map f (list_of_fset A))\<close>
      unfolding list_of_fset_def
      by (smt (verit, del_insts) exists_fset_of_list fset_of_list.rep_eq imageI list.set_map
          notin_fset someI_ex)
  qed
next
  show \<open>set (map f (list_of_fset A)) \<subseteq> f ` fset A\<close>
  proof
    fix v
    assume \<open>v \<in> set (map f (list_of_fset A))\<close>
    then obtain a where "a |\<in>| A" "f a = v"
      unfolding list_of_fset_def
      by (smt (verit, best) exists_fset_of_list fset_of_list.rep_eq imageE list.set_map notin_fset 
          someI_ex)
    then show \<open>v \<in> f ` fset A\<close>
      by (simp add: fmember.rep_eq rev_image_eqI)
  qed
qed

lemma equiv_prop_sema1_sema2:
  \<open>(\<forall>F\<in>AF_proj_to_formula_set_set \<N>. \<exists>f\<in>F. formula_semantics (to_valuation J) f) \<longleftrightarrow>
   (\<forall>F\<in>AF_proj_to_formula_set \<N>. formula_semantics (to_valuation J) F)\<close>
  using equiv_prop_entail2_sema2 equiv_prop_entail2_sema by auto


lemma equiv_enabled_assertions_sema:
  \<open>(enabled_set \<N> J) \<longleftrightarrow> (\<forall>F\<in>AF_assertions_to_formula_set \<N>. formula_semantics (to_valuation J) F)\<close>
  unfolding enabled_projection_def enabled_def enabled_set_def
proof
  assume enab_N: \<open>\<forall>\<C>\<in>\<N>. fset (A_of \<C>) \<subseteq> total_strip J\<close> 
  show \<open>\<forall>F\<in>AF_assertions_to_formula_set \<N>. formula_semantics (to_valuation J) F\<close>
  proof
    fix F
    assume F_in: \<open>F \<in> AF_assertions_to_formula_set \<N>\<close>
    then obtain \<C> where \<C>_in: \<open>\<C> \<in> \<N>\<close> and 
      F_from_\<C>: \<open>F = BigAnd (map sign_to_atomic_formula (list_of_fset (A_of \<C>)))\<close>
      unfolding AF_assertions_to_formula_def AF_assertions_to_formula_set_def by auto
    have \<open>\<forall>f\<in>set (map sign_to_atomic_formula (list_of_fset (A_of \<C>))).
      formula_semantics (to_valuation J) f\<close>
    proof
      fix f
      assume f_in: \<open>f \<in> set (map sign_to_atomic_formula (list_of_fset (A_of \<C>)))\<close>
      define L where \<open>L = (list_of_fset (A_of \<C>))\<close>
      then obtain a v where f_is: \<open>sign_to_atomic_formula a = f\<close> and a_in: \<open>a \<in> set L\<close>
        and v_is: \<open>to_V a = v\<close>
        using f_in by auto
      have \<open>a \<in> fset (A_of \<C>)\<close>
        using a_in unfolding L_def by (smt (verit, ccfv_threshold) exists_fset_of_list
            fset_of_list.rep_eq list_of_fset_def someI_ex)
      then have a_in: \<open>a \<in> total_strip J\<close>
        using enab_N \<C>_in by blast
      consider (Pos) "a = Pos v" | (Neg) \<open>a = Neg v\<close>
        using v_is is_Neg_to_V is_Pos_to_V by blast
      then show \<open>formula_semantics (to_valuation J) f\<close>
      proof cases
        case Pos
        then have \<open>f = Atom v\<close> using f_is by auto
        then show ?thesis
          using a_in unfolding to_valuation_def belong_to_total_def belong_to_def
          by (simp add: Pos)
      next
        case Neg
        then have \<open>f = Not (Atom v)\<close> using f_is by auto
        then show ?thesis
          using a_in Neg to_valuation_def val_strip_neg by force
      qed
    qed
    then show \<open>formula_semantics (to_valuation J) F\<close>
      using BigAnd_semantics[of "to_valuation J"
          "map sign_to_atomic_formula (list_of_fset (A_of \<C>))"] F_from_\<C> by blast
  qed
next
  assume F_sat: \<open>\<forall>F\<in>AF_assertions_to_formula_set \<N>. formula_semantics (to_valuation J) F\<close>
  have \<open>\<forall>\<C>\<in>\<N>. \<forall>a\<in>fset (A_of \<C>). a \<in> total_strip J\<close>
  proof clarify
    fix \<C> a
    assume 
      \<C>_in: \<open>\<C> \<in> \<N>\<close> and
      a_in: \<open>a \<in> fset (A_of \<C>)\<close>
    define F where \<open>F = AF_assertions_to_formula \<C>\<close>
    then have \<open>F \<in> AF_assertions_to_formula_set \<N>\<close>
      unfolding AF_assertions_to_formula_set_def using \<C>_in by blast
    then have \<open>formula_semantics (to_valuation J) F\<close> using F_sat by blast
    then have all_f_sat: \<open>\<forall>f\<in>set (map sign_to_atomic_formula (list_of_fset (A_of \<C>))).
      formula_semantics (to_valuation J) f\<close>
      using BigAnd_semantics[of "to_valuation J"] unfolding F_def AF_assertions_to_formula_def
      by simp
    define f where \<open>f = sign_to_atomic_formula a\<close>
    then have \<open>f \<in> set (map sign_to_atomic_formula (list_of_fset (A_of \<C>)))\<close>
      using a_in fset_map2 by fastforce
    then have f_sat: \<open>formula_semantics (to_valuation J) f\<close>
      using all_f_sat by auto
    then show \<open>a \<in> total_strip J\<close>
      using f_def unfolding to_valuation_def
      by (metis f_sat belong_to.rep_eq belong_to_total.rep_eq formula_semantics.simps(1)
          formula_semantics.simps(3) sign_to_atomic_formula.elims val_strip_neg)
  qed
  then show \<open>\<forall>\<C>\<in>\<N>. fset (A_of \<C>) \<subseteq> total_strip J\<close> by blast
qed

definition sound_propositional_model :: "'v total_interpretation \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool"
  (infix "\<Turnstile>s\<^sub>p" 50) where
  \<open>J \<Turnstile>s\<^sub>p \<N> \<equiv> (bot \<notin> ((enabled_projection (propositional_projection \<N>) J)) \<or>
    \<not> sound_consistent J)\<close>

definition propositionally_unsatisfiable :: "('f, 'v) AF set \<Rightarrow> bool" where
  \<open>propositionally_unsatisfiable \<N> \<equiv> \<forall>J. \<not> (J \<Turnstile>\<^sub>p \<N>)\<close>

(* TODO: move in Sema? *)
lemma unsat_simp: 
  assumes 
    \<open>\<not> sat (S' \<union> S::'v formula set)\<close>
    \<open>sat S'\<close>
    \<open>\<Union> (atoms ` S') \<inter> \<Union> (atoms ` S) = {}\<close>
  shows
    \<open>\<not> sat S\<close>
  unfolding sat_def
proof
  assume contra: \<open>\<exists>\<A>. \<forall>F\<in>S. formula_semantics \<A> F\<close>
  then obtain \<A>S where AS_is: \<open>\<forall>F\<in>S. formula_semantics \<A>S F\<close> by blast
  obtain \<A>F where AF_is: \<open>\<forall>F\<in>S'. formula_semantics \<A>F F\<close> using assms(2) unfolding sat_def by blast
  define \<A> where \<open>\<A> = (\<lambda>a. if a \<in> \<Union> (atoms ` S') then \<A>F a else \<A>S a)\<close>
  have \<open>\<forall>F\<in>S'. formula_semantics \<A> F\<close>
    using AF_is relevant_atoms_same_semantics unfolding \<A>_def
    by (smt (verit, best) UN_I)
  moreover have \<open>\<forall>F\<in>S. formula_semantics \<A> F\<close>
    using AS_is relevant_atoms_same_semantics assms(3) unfolding \<A>_def
    by (smt (verit, del_insts) Int_iff UN_I empty_iff)
  ultimately have \<open>\<forall>F'\<in>(S'\<union>S). formula_semantics \<A> F'\<close> by blast
  then show False
    using assms(1) unfolding sat_def by blast
qed

lemma proj_to_form_un: \<open>AF_proj_to_formula_set (A \<union> B) = 
  AF_proj_to_formula_set A \<union> AF_proj_to_formula_set B\<close>
  unfolding AF_proj_to_formula_set_def propositional_projection_def by blast

lemma unsat_AF_simp: 
  assumes 
    \<open>\<not> sat (AF_proj_to_formula_set (S' \<union> S))\<close>
    \<open>sat (AF_proj_to_formula_set S')\<close>
    \<open>\<Union> (atoms ` (AF_proj_to_formula_set S')) \<inter> \<Union> (atoms ` (AF_proj_to_formula_set S)) = {}\<close>
  shows
    \<open>\<not> sat (AF_proj_to_formula_set S)\<close>
  using unsat_simp assms proj_to_form_un by metis


lemma \<open>to_V ` (set (list_of_fset A)) = to_V ` (fset A)\<close>
  sorry

lemma atoms_simp: \<open>\<Union> (atoms ` (AF_proj_to_formula_set S)) = to_V ` \<Union> (fset ` (A_of ` (proj\<^sub>\<bottom> S)))\<close>
proof
  show \<open>\<Union> (atoms ` AF_proj_to_formula_set S) \<subseteq> to_V ` \<Union> (fset ` A_of ` (proj\<^sub>\<bottom> S))\<close>
  proof
    fix v
    assume \<open>v \<in> \<Union> (atoms ` AF_proj_to_formula_set S)\<close>
    then show \<open>v \<in> to_V ` \<Union> (fset ` A_of ` (proj\<^sub>\<bottom> S))\<close>
      unfolding atoms_def AF_proj_to_formula_set_def AF_to_formula_def
      sorry
  qed
next
  show \<open>to_V ` \<Union> (fset ` A_of ` proj\<^sub>\<bottom>  S) \<subseteq> \<Union> (atoms ` AF_proj_to_formula_set S)\<close>
    sorry
qed

lemma val_from_interp: \<open>\<forall>\<A>. \<exists>J. \<A> = to_valuation J\<close>
proof
  fix \<A>
  define J_bare where \<open>J_bare = {Pos a |(a::'v). \<A> a} \<union> {Neg a |a. \<not> \<A> a}\<close>
  then have interp_J_bare: \<open>is_interpretation J_bare\<close>
    unfolding is_interpretation_def
    by force
  then have total_J_bare: \<open>total (interp_of J_bare)\<close>
    unfolding total_def using J_bare_def
    by (metis (mono_tags, lifting) Abs_propositional_interpretation_inverse Un_iff belong_to.rep_eq
        mem_Collect_eq to_V.simps)
  define J where \<open>J = total_interp_of J_bare\<close>
  have \<open>\<A> = to_valuation J\<close>
  proof
    fix a::'v
    show \<open>\<A> a = to_valuation J a\<close>
      using J_def J_bare_def Abs_propositional_interpretation_inverse 
        Abs_total_interpretation_inverse interp_J_bare total_J_bare to_valuation_def val_strip_pos
      by fastforce
  qed
  then show \<open>\<exists>J. \<A> = to_valuation J\<close>
    by fast
qed

lemma interp_from_val: \<open>\<forall>J. \<exists>\<A>. \<A> = to_valuation J\<close>
  unfolding to_valuation_def by auto


(* TODO: move in Compactness? *)
lemma compactness_unsat: \<open>(\<not> sat (S::'v formula set)) \<longleftrightarrow> (\<exists>s\<subseteq>S. finite s \<and> \<not> sat s)\<close>
  using compactness[of S] unfolding fin_sat_def by blast

lemma never_enabled_finite_subset: 
  \<open>\<forall>J. \<not> enabled_set \<N> J \<Longrightarrow> \<exists>\<N>'\<subseteq>\<N>. finite \<N>' \<and> (\<forall>J. \<not> enabled_set \<N>' J)\<close>
proof -
  assume not_enab_N: \<open>\<forall>J. \<not> enabled_set \<N> J\<close>
  then have \<open>\<not> sat (AF_assertions_to_formula_set \<N>)\<close>
    unfolding sat_def using equiv_enabled_assertions_sema[of \<N>] val_from_interp
    by metis
  then obtain S' where S'_sub: \<open>S' \<subseteq> AF_assertions_to_formula ` \<N>\<close> and S'_fin: \<open>finite S'\<close> and
    S'_unsat: \<open>\<not> sat S'\<close>
    using compactness_unsat unfolding AF_assertions_to_formula_set_def by metis
  obtain \<N>' where N'_sub: \<open>\<N>' \<subseteq> \<N>\<close> and N'_fin: \<open>finite \<N>'\<close>
    and S'_im: \<open>S' = AF_assertions_to_formula ` \<N>'\<close>
    using finite_subset_image[OF S'_fin S'_sub] by blast
  have not_enab_N': \<open>\<forall>J. \<not> enabled_set \<N>' J\<close>
    using equiv_enabled_assertions_sema[of \<N>'] S'_unsat S'_im interp_from_val 
    unfolding sat_def AF_assertions_to_formula_set_def by blast
  then show \<open>\<exists>\<N>' \<subseteq> \<N>. finite \<N>' \<and> (\<forall>J. \<not> enabled_set \<N>' J)\<close>
    using N'_sub N'_fin by auto
qed


lemma compactness_AF_proj: \<open>(\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>) \<longleftrightarrow> (\<exists>\<N>'\<subseteq>\<N>. finite \<N>' \<and> (\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>'))\<close>
proof -
  define \<F> where \<open>\<F> = AF_proj_to_formula_set \<N>\<close>
  have \<open>(\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>) \<longleftrightarrow> (\<forall>J. \<exists>F\<in>\<F>. \<not> formula_semantics (to_valuation J) F)\<close>
    by (simp add: \<F>_def equiv_prop_entail2_sema2)
  also have 
    \<open>(\<forall>J. \<exists>F\<in>\<F>. \<not> formula_semantics (to_valuation J) F) \<longleftrightarrow> (\<forall>\<A>. \<exists>F\<in>\<F>. \<not> formula_semantics \<A> F)\<close>
    using val_from_interp by metis
  also have \<open>(\<forall>\<A>. \<exists>F\<in>\<F>. \<not> formula_semantics \<A> F) \<longleftrightarrow> (\<not> sat \<F>)\<close>
    unfolding sat_def by blast
  also have \<open>(\<not> sat \<F>) \<longleftrightarrow> (\<exists>\<F>'\<subseteq>\<F>. finite \<F>' \<and> \<not> sat \<F>')\<close>
    using compactness_unsat[of \<F>] .
  also have \<open>(\<exists>\<F>'\<subseteq>\<F>. finite \<F>' \<and> \<not> sat \<F>') \<longleftrightarrow> (\<exists>\<F>'\<subseteq>\<F>. finite \<F>' \<and> (\<forall>\<A>. \<exists>F\<in>\<F>'. \<not> formula_semantics \<A> F))\<close>
    unfolding sat_def by auto
  also have \<open>... \<longleftrightarrow> (\<exists>\<F>'\<subseteq>\<F>. finite \<F>' \<and> (\<forall>J. \<exists>F\<in>\<F>'. \<not> formula_semantics (to_valuation J) F))\<close>
    by (metis val_from_interp)
  also have \<open>... \<longleftrightarrow> (\<exists>\<N>'\<subseteq>\<N>. finite \<N>' \<and> (\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>'))\<close>
  proof
    assume \<open>\<exists>\<F>'\<subseteq>\<F>. finite \<F>' \<and> (\<forall>J. \<exists>F\<in>\<F>'. \<not> formula_semantics (to_valuation J) F)\<close>
    then obtain \<F>' where F'_sub: \<open>\<F>'\<subseteq>\<F>\<close> and F'_fin: \<open>finite \<F>'\<close> and
      F'_unsat: \<open>\<forall>J. \<exists>F\<in>\<F>'. \<not> formula_semantics (to_valuation J) F\<close>
      by auto
    have \<open>\<forall>F\<in>\<F>'. \<exists>\<C>\<in>(proj\<^sub>\<bottom> \<N>). AF_to_formula \<C> = F\<close>
      using F'_sub \<F>_def unfolding AF_proj_to_formula_set_def by blast
    then obtain \<N>' where F'_is_map: \<open>\<F>' = AF_to_formula ` \<N>'\<close> and N'_in_proj: \<open>\<N>' \<subseteq> proj\<^sub>\<bottom> \<N>\<close> and
      N'_fin: \<open>finite \<N>'\<close>
      using F'_fin
      by (metis AF_proj_to_formula_set_def F'_sub \<F>_def finite_subset_image)
    have \<open>proj\<^sub>\<bottom> \<N>' = \<N>'\<close>                               
      using N'_in_proj unfolding propositional_projection_def by blast
    then have F'_is: \<open>\<F>' = AF_proj_to_formula_set \<N>'\<close>
      unfolding AF_proj_to_formula_set_def using F'_is_map by simp
    have N'_sub: \<open>\<N>' \<subseteq> \<N>\<close>
      using prop_proj_in N'_in_proj by auto
    have N'_unsat: \<open>\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>'\<close>
      using equiv_prop_entail2_sema2[of _ \<N>'] F'_is F'_unsat 
      by blast
    show \<open>\<exists>\<N>'\<subseteq>\<N>. finite \<N>' \<and> (\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>')\<close>
      using N'_sub N'_fin N'_unsat by blast
  next
    assume \<open>\<exists>\<N>'\<subseteq>\<N>. finite \<N>' \<and> (\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>')\<close>
    then obtain \<N>' where N'_sub: \<open>\<N>' \<subseteq> \<N>\<close> and N'_fin: \<open>finite \<N>'\<close> and N'_unsat: \<open>\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>'\<close>
      by auto
    define \<F>' where \<open>\<F>' = AF_proj_to_formula_set \<N>'\<close>
    then have \<open>\<F>' \<subseteq> \<F>\<close>
      using N'_sub unfolding \<F>_def AF_proj_to_formula_set_def propositional_projection_def by blast
    moreover have \<open>finite \<F>'\<close>
      using \<F>'_def N'_fin unfolding AF_proj_to_formula_set_def propositional_projection_def by simp
    moreover have \<open>\<forall>J. \<exists>F\<in>\<F>'. \<not> formula_semantics (to_valuation J) F\<close>
      using N'_unsat equiv_prop_entail2_sema2[of _ \<N>'] unfolding \<F>'_def by blast
    ultimately show \<open>\<exists>\<F>'\<subseteq>\<F>. finite \<F>' \<and> (\<forall>J. \<exists>F\<in>\<F>'. \<not> formula_semantics (to_valuation J) F)\<close>
      by auto
  qed
  finally show \<open>(\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>) \<longleftrightarrow> (\<exists>\<N>'\<subseteq>\<N>. finite \<N>' \<and> (\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>'))\<close>
    .
qed


definition \<E>_from :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> where
  \<open>\<E>_from \<N> \<equiv> {Pair bot {|neg a|} |a. \<exists>\<C>\<in>\<N>. a \<in> fset (A_of \<C>)}\<close>

lemma prop_proj_\<E>_from: \<open>proj\<^sub>\<bottom> (\<E>_from \<N>) = \<E>_from \<N>\<close>
  unfolding propositional_projection_def \<E>_from_def by auto

lemma prop_proj_sub: \<open>proj\<^sub>\<bottom> \<N> = \<N> \<Longrightarrow> \<N>' \<subseteq> \<N> \<Longrightarrow> proj\<^sub>\<bottom> \<N>' = \<N>'\<close>
  unfolding propositional_projection_def by blast

lemma prop_proj_distrib: \<open>proj\<^sub>\<bottom> (A \<union> B) = proj\<^sub>\<bottom> A \<union> proj\<^sub>\<bottom> B\<close>
  unfolding propositional_projection_def by blast

lemma equiv_\<E>_enabled_\<N>:
  shows \<open>J \<Turnstile>\<^sub>p2 \<E>_from \<N> \<longleftrightarrow> enabled_set \<N> J\<close>
  unfolding propositional_model2_def enabled_set_def enabled_def propositional_projection_def
    enabled_projection_def
proof
  assume empty_proj_E: \<open>{} = {F_of \<C> |\<C>. \<C> \<in> {\<C> \<in> \<E>_from \<N>. F_of \<C> = bot} \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
  have \<open>\<forall>\<C>\<in>\<E>_from \<N>. F_of \<C> = bot\<close> using \<E>_from_def[of \<N>] by auto
  then have a_in_E: \<open>\<forall>\<C>\<in>\<E>_from \<N>. \<exists>a\<in>fset (A_of \<C>). a \<notin> total_strip J\<close>
    using empty_proj_E by blast
  then have \<open>\<forall>\<C>\<in>\<E>_from \<N>. \<forall>a\<in>fset (A_of \<C>). a \<notin> total_strip J\<close>
    unfolding \<E>_from_def by fastforce
  moreover have \<open>\<forall>\<C>\<in>\<N>. \<forall>a\<in>fset (A_of \<C>). \<exists>\<C>'\<in>\<E>_from \<N>. neg a \<in> fset (A_of \<C>')\<close>
    unfolding \<E>_from_def by fastforce
  ultimately have \<open>\<forall>\<C>\<in>\<N>. \<forall>a\<in>fset (A_of \<C>). a \<in> total_strip J\<close>
    by fastforce
  then show \<open>\<forall>\<C>\<in>\<N>. fset (A_of \<C>) \<subseteq> total_strip J\<close>
    by blast
next
  assume enabled_\<C>: \<open>\<forall>\<C>\<in>\<N>. fset (A_of \<C>) \<subseteq> total_strip J\<close>
  have \<open>\<forall>\<C>\<in>\<E>_from \<N>. \<forall>a\<in>fset (A_of \<C>). \<exists>\<C>'\<in>\<N>. neg a \<in> fset (A_of \<C>')\<close>
    unfolding \<E>_from_def
    by (smt (verit) AF.exhaust_sel AF.inject bot_fset.rep_eq empty_iff finsert.rep_eq insertE
        is_Pos.cases mem_Collect_eq neg.simps)
  then have \<open>\<forall>\<C>\<in>\<E>_from \<N>. \<forall>a\<in>fset (A_of \<C>). a \<notin> total_strip J\<close>
    using enabled_\<C> by (meson belong_to.rep_eq neg_prop_interp subsetD)
  then have \<open>\<forall>\<C>\<in>\<E>_from \<N>. (\<not> fset (A_of \<C>) \<subseteq> total_strip J)\<close>
    using \<E>_from_def by fastforce
  then show \<open>{} = {F_of \<C> |\<C>. \<C> \<in> {\<C> \<in> \<E>_from \<N>. F_of \<C> = bot} \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
    by blast
qed


(* definition to_formula :: "'v sign set \<Rightarrow> 'v formula" where
\<open>finite A \<Longrightarrow> to_formula A = \<close> *)
(*
fun to_formula :: "'v sign list \<Rightarrow> 'v formula" where
  \<open>to_formula A = BigAnd (map to_atomic_formula A)\<close>

find_theorems name: linorder
end

(* attempt at proving that a countable type is a linorder
subclass (in countable) linorder
proof
qed
 
*)

term "a:: nat option"

subclass (in countable) ord
subclass (in countable) preorder
subclass (in countable) linorder
subclass (in countable) wellorder


context AF_calculus
begin
fun set_to_formula :: "'v sign set \<Rightarrow> 'v formula" where
  \<open>set_to_formula A = to_formula (sorted_list_of_set A)\<close>

fun AF_to_formula :: "('f, ('v::countable)) AF \<Rightarrow> 'v formula" where
  \<open>AF_to_formula (Pair bot A) = to_formula (sorted_list_of_set A)\<close>
*)


thm compactness
thm compact_entailment
thm finite_set
thm linorder_class.set_sorted_list_of_set
 
definition AF_entails :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>A\<^sub>F" 50) where
  \<open>AF_entails \<M> \<N> \<equiv> (\<forall>J. (enabled_set \<N> J \<longrightarrow> \<M> proj\<^sub>J J \<Turnstile> F_of ` \<N>))\<close>


lemma \<open>enabled_set {} J\<close>
  unfolding enabled_set_def by blast

lemma \<open>(\<forall>J. \<not> (enabled_set \<N> J)) \<Longrightarrow> (\<M> \<Turnstile>\<^sub>A\<^sub>F \<N>)\<close>
  unfolding AF_entails_def by blast
  
definition AF_entails_sound :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool" (infix "\<Turnstile>s\<^sub>A\<^sub>F" 50) where
  \<open>AF_entails_sound \<M> \<N> \<equiv> (\<forall>J. (enabled_set \<N> J \<longrightarrow>
  sound_cons.entails_neg ((fml_ext ` (total_strip J)) \<union> (Pos ` (\<M> proj\<^sub>J J))) (Pos ` F_of ` \<N>)))\<close>


lemma distrib_proj: \<open>\<M> \<union> \<N> proj\<^sub>J J = (\<M> proj\<^sub>J J) \<union> (\<N> proj\<^sub>J J)\<close>
  unfolding enabled_projection_def by auto

lemma distrib_proj_singleton: \<open>\<M> \<union> {\<C>} proj\<^sub>J J = (\<M> proj\<^sub>J J) \<union> ({\<C>} proj\<^sub>J J)\<close>
  unfolding enabled_projection_def by auto

lemma enabled_union2: \<open>enabled_set (\<M> \<union> \<N>) J \<Longrightarrow> enabled_set \<N> J\<close>
  unfolding enabled_set_def by blast

lemma enabled_union1: \<open>enabled_set (\<M> \<union> \<N>) J \<Longrightarrow> enabled_set \<M> J\<close>
  unfolding enabled_set_def by blast

lemma finite_subset_image_strong:
  assumes "finite U" and
    "(\<forall>C \<in> U. (\<exists>D \<in> W. P D = C \<and> Q D))"
  shows "\<exists>W'\<subseteq>W. finite W' \<and> U = P ` W' \<and> (\<forall>D'\<in> W'. Q D')"
  using assms
proof (induction U rule: finite_induct)
  case empty
  then show ?case by blast
next
  case (insert D' U)
  then obtain C' W'' where wpp_and_cp_assms: "W'' \<subseteq> W" "finite W''" "U = P ` W''" "\<forall>a \<in> W''. Q a"
    "C' \<in> W" "P C' = D'" "Q C'"
    by auto
  define W' where "W' = insert C' W''"
  then have \<open>(insert C' W') \<subseteq>W \<and> finite (insert C' W') \<and> insert D' U = P ` (insert C' W') \<and>
             (\<forall>a\<in>(insert C' W'). Q a)\<close>
    using wpp_and_cp_assms by blast
  then show ?case
    by blast
qed

lemma all_to_ex: \<open>\<forall>x. P x \<Longrightarrow> \<exists>x. P x\<close> for P by blast

lemma three_skolems:
  assumes \<open>\<And>U. P U  \<Longrightarrow> \<exists>X Y Z. Q U X Y Z\<close>
  shows \<open>(\<And>X_of Y_of Z_of. (\<And>U. P U \<Longrightarrow> Q U (X_of U) (Y_of U) (Z_of U)) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  using assms
  by metis

lemma finite_subset_with_prop:
  assumes \<open>\<exists>Js. A = f ` Js \<and> (\<forall>J\<in>Js. P J)\<close> and
    \<open>finite C\<close> and
    \<open>B = C \<inter> A\<close>
  shows \<open>\<exists>Js. B = f ` Js \<and> (\<forall>J\<in>Js. P J) \<and> finite Js\<close>
proof -
  have B_fin: \<open>finite B\<close> using assms(2) assms(3) by simp
  have B_sub: \<open>B \<subseteq> A\<close> using assms(2) assms(3) by auto
  obtain Js where A_is: \<open>A = f ` Js\<close> and P_Js: \<open>\<forall>J\<in>Js. P J\<close>
    using assms(1) by blast
  then have \<open>\<forall>b\<in>B. \<exists>J\<in>Js. b = f J \<and> P J\<close>
    using B_sub by blast
  then obtain Js' where \<open>B = f ` Js'\<close> and \<open>finite Js'\<close> \<open>\<forall>J\<in>Js'. P J\<close>
    using B_fin by (smt (verit, ccfv_threshold) B_sub assms(1) finite_subset_image subsetD)
  then show \<open>\<exists>Js. B = f ` Js \<and> (\<forall>J\<in>Js. P J) \<and> finite Js\<close>
    by blast
qed

  (* Splitting report Lemma 4, 1/2 *)
sublocale AF_cons_rel: consequence_relation "to_AF bot" AF_entails
proof
  show \<open>{to_AF bot} \<Turnstile>\<^sub>A\<^sub>F {}\<close>
    unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def
    using bot_entails_empty by simp
next
  fix \<C>
  show \<open>{\<C>} \<Turnstile>\<^sub>A\<^sub>F {\<C>}\<close>
    unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def enabled_set_def
    using entails_reflexive by simp
next
  fix \<M> \<N> \<P> \<Q>
  assume m_in_n: \<open>\<M> \<subseteq> \<N>\<close> and
    p_in_q: \<open>\<P> \<subseteq> \<Q>\<close> and
    m_entails_p: \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F \<P>\<close>
  show \<open>\<N> \<Turnstile>\<^sub>A\<^sub>F \<Q>\<close>
    unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def enabled_set_def
  proof (rule allI, rule impI)
    fix J
    assume q_enabled: \<open>\<forall>\<C>\<in>\<Q>. fset (A_of \<C>) \<subseteq> total_strip J\<close>
    have \<open>{F_of \<C> |\<C>. \<C> \<in> \<M> \<and> fset (A_of \<C>) \<subseteq> total_strip J} \<subseteq> 
      {F_of \<C> |\<C>. \<C> \<in> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
      using m_in_n by blast
    moreover have \<open>F_of ` \<P> \<subseteq> F_of ` \<Q>\<close>
      using p_in_q by blast
    ultimately show \<open>{F_of \<C> |\<C>. \<C> \<in> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J} \<Turnstile> F_of ` \<Q>\<close>
      using m_entails_p  entails_subsets
      unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def enabled_set_def
      by (metis (mono_tags, lifting) q_enabled p_in_q subset_iff)
  qed
next
  fix \<M> \<N> \<C> \<M>' \<N>'
  assume
    entails_c: \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F \<N> \<union> {\<C>}\<close> and
    c_entails: \<open>\<M>' \<union> {\<C>} \<Turnstile>\<^sub>A\<^sub>F \<N>'\<close>
  show \<open>\<M> \<union> \<M>' \<Turnstile>\<^sub>A\<^sub>F \<N> \<union> \<N>'\<close>
    unfolding AF_entails_def
  proof (intro allI impI)
    fix J
    assume enabled_n: \<open>enabled_set (\<N> \<union> \<N>') J\<close>
    {
      assume enabled_c: \<open>enabled_set {\<C>} J\<close>
      then have proj_enabled_c: \<open>{\<C>} proj\<^sub>J J = {F_of \<C>}\<close> 
        unfolding enabled_projection_def using enabled_set_def by blast 
      have cut_hyp1: \<open>\<M> proj\<^sub>J J \<Turnstile> F_of ` \<N> \<union> {F_of \<C>}\<close>
        using entails_c enabled_n enabled_c unfolding AF_entails_def by (simp add: enabled_set_def)
      have \<open>(\<M>' \<union> {\<C>}) proj\<^sub>J J \<Turnstile> F_of ` \<N>'\<close>
        using c_entails enabled_union2[of \<N> \<N>' J, OF enabled_n] unfolding AF_entails_def by simp
      then have cut_hyp2: \<open>(\<M>' proj\<^sub>J J) \<union> {F_of \<C>} \<Turnstile> F_of ` \<N>'\<close>
        using proj_enabled_c distrib_proj_singleton by metis
      have \<open>\<M> \<union> \<M>' proj\<^sub>J J \<Turnstile> F_of ` (\<N> \<union> \<N>')\<close>
        using entails_cut[OF cut_hyp1 cut_hyp2] distrib_proj by (simp add: image_Un) 
    }
    moreover
        {
      assume not_enabled_c: \<open>\<not> enabled_set {\<C>} J\<close>
      then have \<open>\<M>' \<union> {\<C>} proj\<^sub>J J = \<M>' proj\<^sub>J J\<close>
        unfolding enabled_projection_def enabled_set_def by auto
      then have \<open>\<M>' proj\<^sub>J J \<Turnstile> F_of ` \<N>'\<close>
        using c_entails enabled_n unfolding AF_entails_def by (metis enabled_union2) 
      then have \<open>\<M> \<union> \<M>' proj\<^sub>J J \<Turnstile> F_of ` (\<N> \<union> \<N>')\<close>
        using entails_subsets by (metis distrib_proj image_Un sup.cobounded2) 
          }
      ultimately show \<open>\<M> \<union> \<M>' proj\<^sub>J J \<Turnstile> F_of ` (\<N> \<union> \<N>')\<close>
        by blast 
    qed
next
  fix \<M> \<N>
  assume m_entails_n: \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F \<N>\<close>
  consider (NotEnabled) \<open>\<forall>J. \<not> enabled_set \<N> J\<close> | (Enabled) \<open>\<exists>J. enabled_set \<N> J\<close> by blast
  then show \<open>\<exists>M' N'. M' \<subseteq> \<M> \<and> N' \<subseteq> \<N> \<and> finite M' \<and> finite N' \<and> M' \<Turnstile>\<^sub>A\<^sub>F N'\<close>
    proof cases
      case NotEnabled
      then obtain \<N>' where N'_sub: \<open>\<N>' \<subseteq> \<N>\<close> and N'_fin: \<open>finite \<N>'\<close> and sub_not_enab: \<open>\<forall>J. \<not> enabled_set \<N>' J\<close>
        using never_enabled_finite_subset[of \<N>] by blast
      obtain \<M>' where \<open>\<M>' \<subseteq> \<M>\<close> and \<open>finite \<M>'\<close> and \<open>\<M>' \<Turnstile>\<^sub>A\<^sub>F \<N>'\<close>
        using sub_not_enab unfolding AF_entails_def by blast
      then show ?thesis using N'_sub N'_fin by blast
    next
      case Enabled
      then obtain J' where J'_is: \<open>enabled_set \<N> J'\<close> by auto
      {
        fix J
        assume enabled_N: \<open>enabled_set \<N> J\<close>
        then have \<open>\<M> proj\<^sub>J J \<Turnstile> F_of ` \<N>\<close>
          using m_entails_n unfolding AF_entails_def by simp 
        then obtain M' N' where mp_proj: \<open>M' \<subseteq> \<M> proj\<^sub>J J\<close> and
          np_proj: \<open>N' \<subseteq> F_of ` \<N>\<close> and mp_fin: \<open>finite M'\<close> and np_fin: \<open>finite N'\<close> and
          mp_entails_np: \<open>M' \<Turnstile> N'\<close>
          using entails_compactness by metis
    
        have mp_with_f_of: \<open>\<forall>C \<in> M'. \<exists>\<C> \<in> \<M>. F_of \<C> = C \<and> enabled \<C> J\<close> 
          using mp_proj unfolding enabled_projection_def by blast
        have \<open>\<exists>\<M>'\<subseteq> \<M>. finite \<M>' \<and> M' = F_of ` \<M>' \<and> enabled_set \<M>' J\<close>
          using finite_subset_image_strong[OF mp_fin mp_with_f_of]
          unfolding enabled_set_def by blast
        then have m_fin_subset: \<open>\<exists>\<M>' \<subseteq> \<M>. finite \<M>' \<and> M' = \<M>' proj\<^sub>J J\<close>
          unfolding enabled_projection_def enabled_set_def by blast
    
        have np_with_f_of: \<open>\<forall>C \<in> N'. \<exists>\<C> \<in> \<N>. F_of \<C> = C\<close> 
          using np_proj unfolding enabled_projection_def by blast
        have n_fin_subset: \<open>\<exists>\<N>'\<subseteq> \<N>. finite \<N>' \<and> N' = F_of ` \<N>'\<close>
          using finite_subset_image[OF np_fin np_proj] .
    
        obtain \<M>' \<N>' where m_n_subs: \<open>\<M>' \<subseteq> \<M>\<close> \<open>\<N>' \<subseteq> \<N>\<close> \<open>finite \<M>'\<close> \<open>finite \<N>'\<close> \<open>M' = \<M>' proj\<^sub>J J\<close> \<open>N' = F_of ` \<N>'\<close>
          using m_fin_subset n_fin_subset by blast 
        then have m_proj: \<open>\<M>' proj\<^sub>J J \<Turnstile> F_of ` \<N>'\<close>
          using mp_entails_np by simp
    
        have enabled_N': \<open>enabled_set \<N>' J\<close>
          using enabled_N m_n_subs(2) unfolding enabled_set_def by blast
        have \<open>finite (\<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> \<N>'})\<close> (*{a. \<exists>\<C>\<in>\<N>'. a \<in> (fset (A_of \<C>)) }\<close>*)
          using m_n_subs(4) by auto
        then obtain A\<^sub>\<J>\<^sub>' where AJ_is: \<open>fset A\<^sub>\<J>\<^sub>' = \<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> \<N>'}\<close>
          by (smt (verit, best) fset_cases mem_Collect_eq)
        define \<J>' where \<open>\<J>' = Pair bot A\<^sub>\<J>\<^sub>' \<close>
        have \<open>\<forall>a\<in>fset (A_of \<J>'). a \<in>\<^sub>t J\<close>
        proof
          fix a
          assume \<open>a \<in> fset (A_of \<J>')\<close>
          then have \<open>\<exists>\<C>\<in>\<N>'. a \<in> fset (A_of \<C>)\<close>
            unfolding \<J>'_def using AJ_is by auto
          then show \<open>a \<in>\<^sub>t J\<close> 
            using enabled_N' unfolding enabled_set_def enabled_def belong_to_total_def belong_to_def
            by auto
        qed
        moreover have \<open>F_of \<J>' = bot\<close>
          unfolding \<J>'_def
          by simp
        moreover have \<open>\<forall>\<C>\<in>\<N>'. fset (A_of \<C>) \<subseteq> fset (A_of \<J>')\<close>
          using AJ_is \<J>'_def by auto
    
        ultimately have 
          \<open>\<exists>\<M>' \<N>' \<J>'. \<M>' \<subseteq> \<M> \<and> \<N>' \<subseteq> \<N> \<and> finite \<M>' \<and> finite \<N>' \<and> \<M>' proj\<^sub>J J \<Turnstile> F_of ` \<N>' \<and>
           enabled_set \<N>' J \<and> F_of \<J>' = bot \<and> (\<forall>a\<in>fset (A_of \<J>'). a \<in>\<^sub>t J) \<and>
          (fset (A_of \<J>') = \<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> \<N>'})\<close>
          using enabled_N' m_n_subs m_proj AJ_is \<J>'_def
          by (metis (mono_tags, lifting) AF.sel(2))
      }
  
    then obtain \<M>'_of \<N>'_of \<J>'_of where 
      fsets_from_J: \<open>enabled_set \<N> J \<Longrightarrow> \<M>'_of J \<subseteq> \<M> \<and> \<N>'_of J \<subseteq> \<N> \<and> finite (\<M>'_of J) \<and> 
        finite (\<N>'_of J) \<and> (\<M>'_of J) proj\<^sub>J J \<Turnstile> F_of ` (\<N>'_of J) \<and> enabled_set (\<N>'_of J) J \<and>
        F_of (\<J>'_of J) = bot \<and> (\<forall>a\<in>fset (A_of (\<J>'_of J)). a \<in>\<^sub>t J) \<and>
        (fset (A_of (\<J>'_of J)) = \<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> (\<N>'_of J)})\<close> for J 
      using three_skolems[of "\<lambda>U. enabled_set \<N> U" 
        "\<lambda>J \<M>' \<N>' \<J>'. \<M>' \<subseteq> \<M> \<and> \<N>' \<subseteq> \<N> \<and> finite \<M>' \<and> finite \<N>' \<and> \<M>' proj\<^sub>J J \<Turnstile> F_of ` \<N>' \<and> 
        enabled_set \<N>' J \<and> F_of \<J>' = bot \<and> (\<forall>a\<in>fset (A_of \<J>'). a \<in>\<^sub>t J) \<and>
        (fset (A_of \<J>') = \<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> \<N>'})"] by fastforce
  
    let ?\<J>'_set = \<open>{\<J>'_of J |J. enabled_set \<N> J}\<close>
    have ex_Js: \<open>\<exists>Js. ?\<J>'_set = \<J>'_of ` Js \<and> (\<forall>J\<in>Js. enabled_set \<N> J)\<close>
      by blast
    have proj_prop_J': \<open>proj\<^sub>\<bottom> ?\<J>'_set = ?\<J>'_set\<close>
      using fsets_from_J unfolding propositional_projection_def by blast
    let ?\<N>'_un = \<open>\<Union>{\<N>'_of J |J. enabled_set \<N> J}\<close>
    have A_of_enabled: \<open>enabled_set \<N> J \<Longrightarrow> (fset (A_of (\<J>'_of J)) =
      \<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> (\<N>'_of J)})\<close> for J
      using fsets_from_J by presburger
    have A_of_eq: \<open>\<Union> (fset ` A_of ` ?\<J>'_set) = \<Union> (fset ` A_of ` ?\<N>'_un)\<close>
    proof -
      have \<open>\<Union> (fset ` A_of ` ?\<J>'_set) = \<Union>{fset (A_of (\<J>'_of J)) |J. enabled_set \<N> J}\<close>
        by blast
      also have \<open>... = \<Union>{\<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> (\<N>'_of J)} |J. enabled_set \<N> J}\<close>
        using A_of_enabled by (metis (no_types, lifting))
      also have \<open>... = \<Union>(fset ` A_of ` ?\<N>'_un)\<close> by blast
      finally show \<open>\<Union>(fset ` A_of ` ?\<J>'_set) = \<Union>(fset ` A_of ` ?\<N>'_un)\<close>.
    qed
  
    have \<open>\<forall>J. \<not> (J \<Turnstile>\<^sub>p2 (?\<J>'_set \<union> (\<E>_from \<N>)))\<close>
    proof -
      have \<open>\<forall>J. (J \<Turnstile>\<^sub>p2 ?\<J>'_set \<longrightarrow> \<not> enabled_set ?\<N>'_un J)\<close>
      proof (intro allI impI)
        fix J
        assume \<open>J \<Turnstile>\<^sub>p2 ?\<J>'_set\<close>
        then have \<open>{} = ?\<J>'_set proj\<^sub>J J\<close>
          using proj_prop_J' unfolding propositional_model2_def by argo
        then have \<open>\<forall>\<J>'\<in>?\<J>'_set. \<not> enabled \<J>' J\<close>
          unfolding enabled_projection_def by blast
        then have \<open>\<forall>\<J>'\<in>?\<J>'_set. \<exists>a\<in>fset (A_of \<J>'). a \<notin> total_strip J\<close>
          unfolding enabled_def by (meson subsetI)
        then have \<open>\<forall>J'. enabled_set \<N> J' \<longrightarrow> (\<exists>a\<in>fset (A_of (\<J>'_of J')). a \<notin> total_strip J)\<close>
          using fsets_from_J by blast
        then obtain a where a_is: \<open>a \<in> fset (A_of (\<J>'_of J'))\<close> \<open>a \<notin> total_strip J\<close> 
          using J'_is by blast
        then have \<open>\<exists>\<C>\<in>(\<N>'_of J'). a \<in> fset (A_of \<C>) \<and> a \<notin> total_strip J\<close>
          using A_of_enabled fsets_from_J J'_is by auto
        then have \<open>\<exists>\<C>\<in>?\<N>'_un. \<exists>a\<in>fset (A_of \<C>). a \<notin> total_strip J\<close>
          unfolding enabled_def enabled_set_def
          using J'_is enabled_def enabled_set_def by auto
        then have \<open>\<exists>\<C>\<in>?\<N>'_un. \<not> (fset (A_of \<C>) \<subseteq> total_strip J)\<close>
          by blast
        then show \<open>\<not> enabled_set ?\<N>'_un J\<close>
          unfolding enabled_set_def enabled_def by blast
      qed
      then have \<open>J \<Turnstile>\<^sub>p2 ?\<J>'_set \<longrightarrow> \<not> enabled_set \<N> J\<close> for J
        by (smt (verit) Union_iff enabled_set_def fsets_from_J mem_Collect_eq subset_eq)
      then have \<open>J \<Turnstile>\<^sub>p2 ?\<J>'_set \<longrightarrow> \<not> (J \<Turnstile>\<^sub>p2 (\<E>_from \<N>))\<close> for J
        using equiv_\<E>_enabled_\<N>[of J \<N>] by blast
      then have \<open>\<forall>J. \<not> (J \<Turnstile>\<^sub>p2 ?\<J>'_set \<and> J \<Turnstile>\<^sub>p2 (\<E>_from \<N>))\<close> by blast
      then show ?thesis
        unfolding propositional_model2_def enabled_projection_def propositional_projection_def
        by fast
    qed
  
    then obtain \<S> where S_sub: \<open>\<S> \<subseteq> ?\<J>'_set \<union> (\<E>_from \<N>)\<close> and S_fin: \<open>finite \<S>\<close> and
      S_unsat: \<open>\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<S>\<close>
      using compactness_AF_proj by meson
    have E_sat: \<open>sat (AF_proj_to_formula_set (\<E>_from \<N>))\<close>
      unfolding sat_def using J'_is equiv_\<E>_enabled_\<N> equiv_prop_entail2_sema2 by blast
    define \<S>\<^sub>\<J> where \<open>\<S>\<^sub>\<J> = \<S> \<inter> ?\<J>'_set\<close>
    define \<S>\<^sub>\<E> where \<open>\<S>\<^sub>\<E> = \<S> \<inter> (\<E>_from \<N>)\<close>
    define \<S>\<^sub>\<E>' where \<open>\<S>\<^sub>\<E>' = \<S>\<^sub>\<E> \<inter> {Pair bot {|neg a|} |a. \<exists>\<C>\<in>\<S>\<^sub>\<J>. a \<in> fset (A_of \<C>)}\<close>
    define \<S>' where \<open>\<S>' = \<S>\<^sub>\<J> \<union> \<S>\<^sub>\<E>'\<close>
    find_theorems "proj\<^sub>\<bottom> _ = _"
    have proj_S':  \<open>proj\<^sub>\<bottom>  \<S>' = \<S>'\<close>
      using proj_prop_J' prop_proj_\<E>_from S_sub prop_proj_sub prop_proj_distrib
      unfolding \<S>'_def \<S>\<^sub>\<J>_def \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def by (smt (verit, best) inf_le1)
    have S_is: \<open>\<S> = (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>') \<union> \<S>'\<close>
      using S_sub \<S>\<^sub>\<J>_def \<S>\<^sub>\<E>_def \<S>'_def \<S>\<^sub>\<E>'_def by blast
    have \<open>to_V ` \<Union> (fset ` A_of ` (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>')) \<inter> to_V ` \<Union> (fset ` A_of ` \<S>') = {}\<close>
    proof -
      {
        fix v
        assume \<open>v \<in> to_V ` \<Union> (fset ` A_of ` (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>'))\<close>
        then have \<open>v \<notin> to_V ` \<Union> (fset ` A_of ` \<S>')\<close> sorry
      }
      moreover {
        fix v
        assume \<open>v \<notin> to_V ` \<Union> (fset ` A_of ` (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>'))\<close>
        then have \<open>v \<in> to_V ` \<Union> (fset ` A_of ` \<S>')\<close> sorry
      }
      ultimately show ?thesis by blast
    qed
    then have empty_inter: \<open>\<Union> (atoms ` (AF_proj_to_formula_set (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>'))) \<inter>
        \<Union> (atoms ` (AF_proj_to_formula_set \<S>')) = {}\<close>
      using atoms_simp proj_S' prop_proj_distrib prop_proj_sub
      by (smt (verit, ccfv_threshold) S_sub Un_subset_iff \<open>\<S> = \<S>\<^sub>\<E> - \<S>\<^sub>\<E>' \<union> \<S>'\<close> proj_prop_J'
          prop_proj_\<E>_from)
    have sat_rest: \<open>sat (AF_proj_to_formula_set (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>'))\<close>
      using E_sat unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def AF_proj_to_formula_set_def
        propositional_projection_def sat_def by blast
    have \<open>\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<S>'\<close>
      using unsat_AF_simp[OF _ sat_rest empty_inter] S_unsat equiv_prop_entail2_sema2 S_is
      val_from_interp unfolding sat_def by metis
    have ex_fin_Js: \<open>\<exists>Js. \<S>\<^sub>\<J> = \<J>'_of ` Js \<and> (\<forall>J\<in>Js. enabled_set \<N> J) \<and> finite Js\<close>
        using finite_subset_with_prop[OF ex_Js S_fin \<S>\<^sub>\<J>_def] .
    then obtain Js where Js_fin: \<open>finite Js\<close> and Js_enab: \<open>\<forall>J\<in>Js. enabled_set \<N> J\<close> and
      Js_is: \<open>\<J>'_of ` Js = \<S>\<^sub>\<J>\<close>
      by blast
  
    define \<M>' where \<open>\<M>' = \<Union>{\<M>'_of J |J. J \<in> Js}\<close>
    define \<N>' where  \<open>\<N>' = \<Union>{\<N>'_of J |J. J \<in> Js}\<close>
    then have \<open>\<M>' \<subseteq> \<M>\<close>
      unfolding \<M>'_def using fsets_from_J Js_enab by fast
    moreover have \<open>\<N>' \<subseteq> \<N>\<close>
      unfolding \<N>'_def using fsets_from_J Js_enab by fast
    moreover have \<open>finite \<M>'\<close>
      unfolding \<M>'_def using fsets_from_J Js_fin Js_enab by auto
    moreover have \<open>finite \<N>'\<close>
      unfolding \<N>'_def using fsets_from_J Js_fin Js_enab by auto
    moreover have \<open>\<M>' \<Turnstile>\<^sub>A\<^sub>F \<N>'\<close> unfolding AF_entails_def
    proof clarsimp
      fix J
      assume \<open>enabled_set \<N>' J\<close>
      have \<open>enabled_set \<N> J\<close>
      proof (rule ccontr)
        assume \<open>\<not> enabled_set \<N> J\<close>
        then have \<open>J \<Turnstile>\<^sub>p2 ?\<J>'_set\<close>
          using equiv_\<E>_enabled_\<N> (* TODO but I'm not sure this will be easy to get *)
          sorry
        show False
          sorry
      qed
      show \<open>\<M>' proj\<^sub>J J \<Turnstile> F_of ` \<N>'\<close>
        sorry
    qed
    ultimately show \<open>\<exists>\<M>' \<N>'. \<M>' \<subseteq> \<M> \<and> \<N>' \<subseteq> \<N> \<and> finite \<M>' \<and> finite \<N>' \<and> \<M>' \<Turnstile>\<^sub>A\<^sub>F \<N>'\<close>
      by blast
  qed
qed


















































end

end

    (* have \<open>\<forall>M' N'. M proj\<^sub>J J \<subseteq> M' \<and> F_of ` N \<subseteq> N' \<and> M' \<union> N' = UNIV \<longrightarrow> M' \<Turnstile> N'\<close>
     * proof clarsimp
     *   fix M' N'
     *   assume proj_m: \<open>M proj\<^sub>J J \<subseteq> M'\<close> and
     *     fn_in_np: \<open>F_of ` N \<subseteq> N'\<close> and
     *     m_n_partition: \<open>M' \<union> N' = UNIV\<close>
     *   show \<open>M' \<Turnstile> N'\<close>
     *   proof (cases "M' \<inter> N' = {}")
     *     case True
     *     define \<N>' where np_def: \<open>\<N>' = {C. F_of C \<in> N' \<and> enabled C J}\<close>
     *     define \<M>' where mp_def: \<open>\<M>' = UNIV - \<N>'\<close>
     *     have \<open>M \<subseteq> \<M>'\<close>
     *     proof
     *       fix x
     *       assume x_in: \<open>x \<in> M\<close>
     *       have \<open>\<not> enabled x J \<or> F_of x \<in> M'\<close>
     *         using proj_m unfolding enabled_def enabled_projection_def using x_in by blast 
     *       then have \<open>x \<notin> \<N>'\<close>
     *         unfolding np_def using True by fastforce 
     *       then show \<open>x \<in> \<M>'\<close>
     *         unfolding mp_def by blast 
     *     qed
     *     moreover have \<open>N \<subseteq> \<N>'\<close>
     *       using fn_in_np enabled_n unfolding np_def enabled_set_def by force 
     *     ultimately have mp_entails_af_np: \<open>\<M>' \<Turnstile>\<^sub>A\<^sub>F \<N>'\<close>
     *       using prem_entails_supsets_af mp_def by simp 
     *     moreover have enabled_np: \<open>enabled_set \<N>' J\<close>
     *       unfolding np_def enabled_set_def by auto
     *     moreover have \<open>F_of ` \<N>' = N'\<close>
     *     proof (intro equalityI subsetI)
     *       fix x
     *       assume \<open>x \<in> F_of ` \<N>'\<close>
     *       then show \<open>x \<in> N'\<close>
     *         unfolding np_def by auto 
     *     next
     *       fix x
     *       assume x_in: \<open>x \<in> N'\<close>
     *       define C where \<open>C = Pair x (total_strip J)\<close>
     *       have \<open>enabled C J\<close>
     *         unfolding C_def enabled_def by auto 
     *       then show \<open>x \<in> F_of ` \<N>'\<close>
     *         unfolding C_def np_def using x_in by force 
     *     qed
     *     moreover have \<open>\<M>' proj\<^sub>J J = M'\<close>
     *     proof (intro equalityI subsetI)
     *       fix x
     *       assume \<open>x \<in> \<M>' proj\<^sub>J J\<close>
     *       then obtain C where f_of_c: \<open>F_of C = x\<close> and c_in: \<open>C \<in> \<M>'\<close> and c_enabled: \<open>enabled C J\<close>
     *         unfolding enabled_projection_def by blast 
     *       then show \<open>x \<in> M'\<close>
     *         using m_n_partition unfolding mp_def np_def by auto
     *     next
     *       fix x
     *       assume x_in: \<open>x \<in> M'\<close>
     *       define C where \<open>C = Pair x (total_strip J)\<close>
     *       then show \<open>x \<in> \<M>' proj\<^sub>J J\<close>
     *         unfolding mp_def np_def enabled_projection_def using True x_in
     *         by (smt (verit, del_insts) AF.sel(1) AF.sel(2) DiffI UNIV_I disjoint_iff enabled_def
     *           mem_Collect_eq order_refl)
     *     qed
     *     ultimately show \<open>M' \<Turnstile> N'\<close>
     *       unfolding AF_entails_def by blast 
     *     next
     *       case False
     *       assume inter_not_empty: \<open>M' \<inter> N' \<noteq> {}\<close>
     *       then obtain C where \<open>C \<in> M' \<inter> N'\<close> by blast 
     *       then show \<open>M' \<Turnstile> N'\<close> using entails_reflexive entails_subsets
     *         by (meson Int_lower1 Int_lower2 entails_cond_reflexive inter_not_empty)
      *     qed

     *     then show \<open>M proj\<^sub>J J \<Turnstile> F_of ` N\<close>
     *       using entails_supsets by presburger 

        *)


  (*
interpretation ext_cons_rel_std: consequence_relation "Pos (to_AF bot)" AF_cons_rel.entails_neg
  using AF_cons_rel.ext_cons_rel .

interpretation sound_cons_rel: consequence_relation "Pos bot" sound_cons.entails_neg
  using sound_cons.ext_cons_rel .
    
lemma [simp]: \<open>F_of ` to_AF ` N = N\<close>
  unfolding to_AF_def by force

lemma [simp]: \<open>to_AF ` M proj\<^sub>J J = M\<close>
  unfolding to_AF_def enabled_projection_def enabled_def by force

lemma [simp]: \<open>enabled_set (to_AF ` N) J\<close>
  unfolding enabled_set_def enabled_def to_AF_def by simp

lemma [simp]: \<open>{to_V C |C. C \<in> Pos ` N \<and> \<not> is_Pos C} = {}\<close>
  by auto
    
lemma [simp]: \<open>{to_V C |C. C \<in> U \<union> Pos ` M \<and> \<not> is_Pos C} = {to_V C |C. C \<in> U \<and> \<not> is_Pos C}\<close>
  by auto

lemma [simp]: \<open>{to_V C |C. C \<in> Pos ` F_of ` N \<and> is_Pos C} = F_of ` N\<close>
  by force 

lemma [simp]: \<open>{C. F_of C \<in> M} proj\<^sub>J J = M\<close>
proof (intro equalityI subsetI)
  fix x
  assume x_in: \<open>x \<in> {C. F_of C \<in> M} proj\<^sub>J J\<close>
  define C where \<open>C = to_AF x\<close>
  then show \<open>x \<in> M\<close> 
    using x_in unfolding enabled_projection_def enabled_def to_AF_def by auto 
next
  fix x
  assume x_in: \<open>x \<in> M\<close>
  define C where \<open>C = to_AF x\<close>
  then show \<open>x \<in>  {C. F_of C \<in> M} proj\<^sub>J J\<close> 
    using x_in unfolding enabled_projection_def enabled_def to_AF_def
    by (metis (mono_tags, lifting) AF.sel(1) AF.sel(2) mem_Collect_eq subsetI)
qed 

lemma [simp]: \<open>F_of ` {C. F_of C \<in> M} = M\<close>
proof (intro equalityI subsetI)
  fix x
  assume x_in: \<open>x \<in> F_of ` {C. F_of C \<in> M}\<close>
  define C where \<open>C = to_AF x\<close>
  then show \<open>x \<in> M\<close>
    using x_in by blast 
next
  fix x
  assume x_in: \<open>x \<in> M\<close>
  define C where \<open>C = to_AF x\<close>
  then show \<open>x \<in> F_of ` {C. F_of C \<in> M}\<close>
    using x_in by (smt (z3) AF.sel(1) imageI mem_Collect_eq) 
qed
  
lemma set_on_union_triple_split: \<open>{f C |C. C \<in> M \<union> N \<union> g J \<and> l C J} = {f C |C. C \<in> M \<and> l C J} \<union>
  {f C |C. C \<in> N \<and> l C J} \<union> {f C |C. C \<in> g J \<and> l C J}\<close>
  by blast 

lemma [simp]: \<open>{F_of C |C. C \<in> {C. F_of C \<in> Q' \<and> \<not> enabled C J} \<and> enabled C J} = {}\<close>
proof (intro equalityI subsetI)
  fix x
  assume x_in: \<open>x \<in> {F_of C |C. C \<in> {C. F_of C \<in> Q' \<and> \<not> enabled C J} \<and> enabled C J}\<close>
  then obtain C where \<open>F_of C = x\<close> and c_in: \<open>C \<in> {C. F_of C \<in> Q' \<and> \<not> enabled C J}\<close> and
    enab_c: \<open>enabled C J\<close>
    by blast
  then have \<open>\<not> enabled C J\<close> using c_in by blast 
  then have \<open>False\<close> using enab_c by auto 
  then show \<open>x \<in> {}\<close> by auto 
qed auto

lemma f_of_simp_enabled [simp]: \<open>{F_of C |C. F_of C \<in> M \<and> enabled C J} = M\<close>
  unfolding enabled_def
  by (smt (z3) AF.sel(1) AF.sel(2) Collect_mono_iff conj_subset_def mem_Collect_eq order_refl
    subset_antisym subset_eq)

lemma [simp]: \<open>F_of ` {C. F_of C \<in> M \<and> enabled C J} = M\<close>
proof -
  have \<open>F_of ` {C. F_of C \<in> M \<and> enabled C J} = {F_of C |C. F_of C \<in> M \<and> enabled C J}\<close>
    by blast 
  then show ?thesis by simp
qed


(* Splitting report Lemma 4, 2/2 *)
interpretation AF_sound_cons_rel: consequence_relation "to_AF bot" AF_entails_sound
proof
  have \<open>{Pos bot} \<subseteq> Pos ` {F_of C |C. C \<in> {to_AF bot} \<and>
    A_of C \<subseteq> total_strip (J :: 'v total_interpretation)}\<close>
    unfolding to_AF_def by simp
  then show \<open>{to_AF bot} \<Turnstile>s\<^sub>A\<^sub>F {}\<close>
    using sound_cons_rel.bot_entails_empty sound_cons_rel.entails_subsets
    unfolding AF_entails_sound_def enabled_def enabled_projection_def
    by (smt (verit, ccfv_threshold) AF.sel(1) AF.sel(2) UnCI bot.extremum image_eqI insertI1
      mem_Collect_eq singletonD subsetI to_AF_def)
next
  fix C :: "('f, 'v) AF"
  have \<open>Pos ` {F_of Ca |Ca. Ca \<in> {C} \<and> A_of Ca \<subseteq> total_strip J} \<subseteq> (Pos ` F_of ` {C})\<close>
    by auto
  show \<open>{C} \<Turnstile>s\<^sub>A\<^sub>F {C}\<close>
    unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
    using sound_cons_rel.entails_reflexive[of "Pos (F_of C)"] sound_cons_rel.entails_subsets 
    by (smt (verit, ccfv_SIG) UnCI empty_subsetI imageI insert_subset mem_Collect_eq singletonI)
next
  fix M N P Q
  assume m_in_n: \<open>M \<subseteq> N\<close> and
    p_in_q: \<open>P \<subseteq> Q\<close> and
    m_entails_p: \<open>M \<Turnstile>s\<^sub>A\<^sub>F P\<close>
  show \<open>N \<Turnstile>s\<^sub>A\<^sub>F Q\<close>
    unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
  proof (rule allI, rule impI)
    fix J
    assume q_enabled: \<open>\<forall>C\<in>Q. A_of C \<subseteq> total_strip J\<close>
    have \<open>{F_of C |C. C \<in> M \<and> A_of C \<subseteq> total_strip J} \<subseteq>
      {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J}\<close>
      using m_in_n by blast
    moreover have \<open>F_of ` P \<subseteq> F_of ` Q\<close>
      using p_in_q by blast
    ultimately show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union>
      Pos ` {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J}) (Pos ` F_of ` Q)\<close>
      using m_entails_p  sound_cons_rel.entails_subsets m_in_n
      unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
      by (smt (z3) Un_iff consequence_relation.entails_subsets imageE image_eqI mem_Collect_eq
        p_in_q q_enabled sound_cons_rel.consequence_relation_axioms subset_iff)
  qed 
next
  fix M N
  assume prem_entails_supsets_af: \<open>\<forall>M' N'. M \<subseteq> M' \<and> N \<subseteq> N' \<and> M' \<union> N' = UNIV \<longrightarrow> M' \<Turnstile>s\<^sub>A\<^sub>F N'\<close>
  show \<open>M \<Turnstile>s\<^sub>A\<^sub>F N\<close>
    unfolding AF_entails_sound_def sound_cons.entails_neg_def
  proof (intro allI impI)
    fix J
    assume enabled_n: \<open>enabled_set N J\<close>
    define P where \<open>P = {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C}  \<union> (M proj\<^sub>J J)\<close>
    define Q where \<open>Q = F_of ` N \<union> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C}\<close>
    have \<open>\<forall>P' Q'. P \<subseteq> P' \<and> Q \<subseteq> Q' \<and> P'\<union>Q' = UNIV \<longrightarrow> P' \<Turnstile>s Q'\<close>
    proof clarsimp
      fix P' Q'
      assume p_sub: \<open>P \<subseteq> P'\<close> and
        q_sub: \<open>Q \<subseteq> Q'\<close> and
        pq_univ: \<open>P' \<union> Q' = UNIV\<close>
      define M' where \<open>M' = M \<union> {C. F_of C \<in> P'} \<union> {C. F_of C \<in> Q' \<and> \<not> enabled C J}\<close>
      define N' where \<open>N' = N \<union> {C. F_of C \<in> Q' \<and> enabled C J}\<close>
      have \<open>M \<subseteq> M'\<close> using M'_def by auto
      moreover have \<open>N \<subseteq> N'\<close> using N'_def by auto
      moreover have \<open>M' \<union> N' = UNIV\<close> unfolding M'_def N'_def using pq_univ by blast 
      ultimately have mp_entails_np: \<open>M' \<Turnstile>s\<^sub>A\<^sub>F N'\<close> using prem_entails_supsets_af by auto 
      have simp_left: \<open>{to_V C |C. (C \<in> fml_ext ` total_strip J \<or> C \<in> Pos ` (M' proj\<^sub>J J))
        \<and> is_Pos C} = {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> (M' proj\<^sub>J J) \<close> for J
        by force 
      have simp_right: \<open>{to_V C |C. (C \<in> fml_ext ` total_strip J \<or> C \<in> Pos ` (M' proj\<^sub>J J))
        \<and> \<not> is_Pos C} = {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} \<union>
        {to_V C |C. C \<in> Pos ` (M' proj\<^sub>J J) \<and> \<not> is_Pos C}\<close> for J
        by blast 
      have \<open>enabled_set N' J\<close>
        unfolding N'_def using enabled_n enabled_set_def by fastforce 
      then have \<open>{to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> (M' proj\<^sub>J J) \<Turnstile>s
        F_of ` N' \<union> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C}\<close>
        using mp_entails_np 
        unfolding AF_entails_sound_def sound_cons.entails_neg_def
        by (simp add: simp_left simp_right)
      moreover have \<open>{to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> (M' proj\<^sub>J J) = P'\<close>
      proof -
        have \<open>{to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> (M' proj\<^sub>J J) =
          {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> 
          {F_of C |C. C \<in> M  \<and> enabled C J} \<union>
          {F_of C |C. C \<in> {C. F_of C \<in> P'} \<and> enabled C J} \<union>
          {F_of C |C. C \<in> {C. F_of C \<in> Q' \<and> \<not> enabled C J} \<and> enabled C J}\<close>
          unfolding enabled_projection_def M'_def
          using set_on_union_triple_split[of F_of M _ _ J enabled]
          by blast 
        also have \<open>{to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> 
          {F_of C |C. C \<in> M  \<and> enabled C J} \<union>
          {F_of C |C. C \<in> {C. F_of C \<in> P'} \<and> enabled C J} \<union>
          {F_of C |C. C \<in> {C. F_of C \<in> Q' \<and> \<not> enabled C J} \<and> enabled C J} =
          {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> 
          {F_of C |C. C \<in> M  \<and> enabled C J} \<union>
          {F_of C |C. C \<in> {C. F_of C \<in> P'} \<and> enabled C J}\<close> by simp
        also have \<open>{to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> 
          {F_of C |C. C \<in> M  \<and> enabled C J} \<union>
          {F_of C |C. C \<in> {C. F_of C \<in> P'} \<and> enabled C J} =
          {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> 
          {F_of C |C. C \<in> M  \<and> enabled C J} \<union> P'\<close> by simp
        also have \<open>{to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> 
          {F_of C |C. C \<in> M  \<and> enabled C J} \<union> P' = P'\<close>
          using p_sub unfolding P_def enabled_projection_def by auto 
        finally show  \<open>{to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> (M' proj\<^sub>J J) = P'\<close> .
      qed
      moreover have \<open>F_of ` N' \<union> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} = Q'\<close>
      proof -
        have \<open>F_of ` N' \<union> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} = 
          F_of ` N \<union> F_of ` {C. F_of C \<in> Q' \<and> enabled C J} \<union>
          {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C}\<close>
          unfolding N'_def by blast 
        also have \<open>F_of ` N \<union> F_of ` {C. F_of C \<in> Q' \<and> enabled C J} \<union>
          {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} = F_of ` N \<union> Q' \<union>
          {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C}\<close> by simp
        also have \<open>F_of ` N \<union> Q' \<union> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} = Q'\<close>
          using Q_def q_sub by blast 
        finally show ?thesis .
      qed
      ultimately show \<open>P' \<Turnstile>s Q'\<close> by auto 
    qed
    then have p_entails_q: \<open>P \<Turnstile>s Q\<close>
      using sound_cons.entails_supsets by auto 
    show \<open>{to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` (M proj\<^sub>J J) \<and> is_Pos C} \<union>
      {to_V C |C. C \<in> Pos ` F_of ` N \<and> \<not> is_Pos C} \<Turnstile>s
      {to_V C |C. C \<in> Pos ` F_of ` N \<and> is_Pos C} \<union>
      {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` (M proj\<^sub>J J) \<and> \<not> is_Pos C}\<close>
    proof -
      have \<open>{to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` (M proj\<^sub>J J) \<and> is_Pos C} \<union>
        {to_V C |C. C \<in> Pos ` F_of ` N \<and> \<not> is_Pos C} = P\<close>
        unfolding P_def by force
      moreover have \<open>{to_V C |C. C \<in> Pos ` F_of ` N \<and> is_Pos C} \<union>
        {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` (M proj\<^sub>J J) \<and> \<not> is_Pos C} = Q\<close>
        unfolding Q_def by auto
      ultimately show ?thesis
        using p_entails_q by auto 
    qed
  qed
qed


lemma sound_entail_tautology: "{} \<Turnstile>s\<^sub>A\<^sub>F {Pair (fml (v::'v)) {Pos v}}"
  unfolding AF_entails_sound_def enabled_projection_def enabled_set_def total_def
    sound_cons.entails_neg_def enabled_def
proof (simp, rule allI, rule impI)
  fix J 
  assume \<open>Pos v \<in> total_strip J\<close>
  then have \<open>fml v \<in> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C}\<close>
    by force
  then show \<open>{to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<Turnstile>s
    insert (fml v) {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C}\<close>
    by (meson Set.insert_mono empty_subsetI insert_subset sound_cons.entails_reflexive
      sound_cons.entails_subsets)
qed
  
  (* this is a counter-example to an early version of the lemma below
   * without the precondition \<not> {} \<Turnstile> {} *)
lemma cex_entailments_inclusion:
  assumes
    tautoAF: \<open>{} \<Turnstile>\<^sub>A\<^sub>F {}\<close> and
    sound_notautoAF: \<open>\<not> ({} \<Turnstile>s\<^sub>A\<^sub>F {to_AF bot})\<close>
  shows \<open>\<exists>C D. proj\<^sub>\<bottom> C \<Turnstile>\<^sub>A\<^sub>F proj\<^sub>\<bottom> D \<and> \<not> (proj\<^sub>\<bottom> C \<Turnstile>s\<^sub>A\<^sub>F proj\<^sub>\<bottom> D)\<close> 
proof (rule exI, rule exI)
  have \<open>\<forall>J. enabled_set {} J\<close> unfolding enabled_set_def enabled_def by blast 
  then have tautoF: \<open>{} \<Turnstile> {}\<close> using tautoAF unfolding AF_entails_def enabled_projection_def by simp
  have empty_entails: \<open>{} \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
    using entails_empty_reflexive_dangerous[OF tautoF] unfolding AF_entails_def by blast 
  define C  :: "('f, 'v) AF set" where \<open>C = {}\<close>
  then have c_is: \<open>proj\<^sub>\<bottom> C = {}\<close> unfolding propositional_projection_def by blast 
  define D :: "('f, 'v) AF set" where \<open>D = {to_AF bot}\<close> 
  then have d_is: \<open>proj\<^sub>\<bottom> D = {to_AF bot}\<close>
    unfolding propositional_projection_def to_AF_def
    by (metis (mono_tags, lifting) AF.sel(1) mem_Collect_eq singletonD subsetI subset_antisym)
  have pos: \<open>proj\<^sub>\<bottom> C \<Turnstile>\<^sub>A\<^sub>F proj\<^sub>\<bottom> D\<close> using c_is d_is empty_entails by auto 
  have neg: \<open>\<not> (proj\<^sub>\<bottom> C \<Turnstile>s\<^sub>A\<^sub>F proj\<^sub>\<bottom> D)\<close> using c_is d_is sound_notautoAF by auto 
  show \<open>proj\<^sub>\<bottom> C \<Turnstile>\<^sub>A\<^sub>F proj\<^sub>\<bottom> D \<and> \<not> proj\<^sub>\<bottom> C \<Turnstile>s\<^sub>A\<^sub>F proj\<^sub>\<bottom> D\<close> using pos neg by auto 
qed

lemma entails_in_sound_entails_for_prop_clauses:
  assumes
    entails_useful: \<open>\<not> {} \<Turnstile>\<^sub>A\<^sub>F {}\<close> and
    entails_nonsound: \<open>proj\<^sub>\<bottom> C\<^sub>1 \<Turnstile>\<^sub>A\<^sub>F proj\<^sub>\<bottom> C\<^sub>2\<close>
  shows \<open>proj\<^sub>\<bottom> C\<^sub>1 \<Turnstile>s\<^sub>A\<^sub>F proj\<^sub>\<bottom> C\<^sub>2\<close>
proof -
  show \<open>proj\<^sub>\<bottom> C\<^sub>1 \<Turnstile>s\<^sub>A\<^sub>F proj\<^sub>\<bottom> C\<^sub>2\<close>
    unfolding AF_entails_sound_def 
  proof
    fix J
    show \<open>enabled_set (proj\<^sub>\<bottom> C\<^sub>2) J \<longrightarrow> sound_cons.entails_neg
      (fml_ext ` total_strip J \<union> Pos ` (proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J)) (Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2)\<close>
    proof
      assume enabled_c2: \<open>enabled_set (proj\<^sub>\<bottom> C\<^sub>2) J\<close>
      have empty_bot_proj_c1: \<open>F_of ` proj\<^sub>\<bottom> C\<^sub>1 = {} \<or> F_of ` proj\<^sub>\<bottom> C\<^sub>1 = {bot}\<close>
        unfolding propositional_projection_def enabled_projection_def by force
      have empty_bot_proj_c2: \<open>F_of ` proj\<^sub>\<bottom> C\<^sub>2 = {} \<or> F_of ` proj\<^sub>\<bottom> C\<^sub>2 = {bot}\<close>
        unfolding propositional_projection_def enabled_projection_def by force
          {
      assume \<open>(proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J) = {}\<close>
      then have \<open>False\<close>
        using entails_useful entails_nonsound empty_bot_proj_c2
        by (metis AF_entails_def enabled_c2 entails_bot_to_entails_empty
          entails_empty_reflexive_dangerous)
            }
      then have c1_to_bot: \<open>(proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J) = {bot}\<close>
        unfolding enabled_projection_def using empty_bot_proj_c1
        by (smt (verit, best) Collect_cong emptyE empty_Collect_eq mem_Collect_eq rev_image_eqI
          singleton_conv2)
      have \<open>Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 = {} \<or> Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 = {Pos bot}\<close>
        unfolding propositional_projection_def enabled_projection_def by force
      then have \<open>{C. C \<in> Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 \<and> \<not> is_Pos C} = {}\<close>
        by auto
      then have c2_to_empty: \<open>{to_V C | C. C \<in> Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 \<and> \<not> is_Pos C} = {}\<close>
        by auto
      have \<open>bot \<in> {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` (proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J) \<and> is_Pos C}\<close>
        using c1_to_bot by force 
      then show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J))
        (Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2)\<close>
        unfolding sound_cons.entails_neg_def
        using sound_cons.bot_entails_empty sound_cons.entails_subsets
        by (smt (z3) c2_to_empty empty_subsetI insert_subset sup_bot.right_neutral)
    qed 
  qed 
qed
  
  (* Splitting report Lemma 5, 1/2 *)
lemma \<open>(to_AF ` M \<Turnstile>\<^sub>A\<^sub>F to_AF ` N) \<equiv> (M \<Turnstile> N)\<close>
  unfolding AF_entails_def by simp

lemma distrib_union_in_set: \<open>{f a |a. a\<in> B \<union> C \<and> D a} = {f a| a. a\<in>B\<and>D a} \<union> {f a| a. a\<in>C \<and> D a}\<close>
  by blast
    
lemma [simp]: \<open>{to_V C |C. C \<in> Pos ` M \<and> is_Pos C} = M\<close>
  by force

lemma finite_subsets_split: \<open>\<forall>J. \<exists>A. finite A \<and> A \<subseteq> B J \<union> C \<Longrightarrow>
  \<exists>A1 A2. finite A1 \<and> finite A2 \<and> A1 \<subseteq> B J \<and> A2 \<subseteq> C\<close>
  by blast 

lemma finite_subset_image_with_prop:
  assumes "finite B"
  shows "B \<subseteq> {f x |x. x \<in> A \<and> P x} \<Longrightarrow> \<exists>C\<subseteq>A. finite C \<and> B = f ` C \<and> (\<forall>x\<in>C. P x)"
  using assms
proof induct
  case empty
  then show ?case by simp
next
  case insert
  then show ?case
    by (clarsimp simp del: image_insert simp add: image_insert [symmetric]) blast
qed

    (* Splitting report Lemma 5, 2/2 *)
lemma \<open>(to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N) \<equiv> (M \<Turnstile>s N)\<close>
proof -
  {
    fix M N
    assume m_to_n: \<open>M \<Turnstile>s N\<close>
    have \<open>to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N\<close>
      unfolding AF_entails_sound_def sound_cons.entails_neg_def 
    proof (simp, rule allI)
      fix J
      have \<open>M \<subseteq> {to_V C |C. (C \<in> fml_ext ` total_strip J \<or> C \<in> Pos ` M) \<and> is_Pos C}\<close>
        by force
      then show \<open>{to_V C |C. (C \<in> fml_ext ` total_strip J \<or> C \<in> Pos ` M) \<and> is_Pos C} \<Turnstile>s
          N \<union> {to_V C |C. (C \<in> fml_ext ` total_strip J \<or> C \<in> Pos ` M) \<and> \<not> is_Pos C}\<close>
        using m_to_n by (meson sound_cons.entails_subsets sup.cobounded1)
    qed
  } moreover {
    fix M N
    assume \<open>to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N\<close>
    have all_bigger_entail: \<open>\<forall>M' N'. (M' \<supseteq> M \<and> N' \<supseteq> N \<and> M' \<union> N' = UNIV) \<longrightarrow> M' \<Turnstile>s N'\<close>
    proof clarsimp 
      fix M' N'
      assume \<open>M \<subseteq> M'\<close> and
        \<open>N \<subseteq> N'\<close> and
        union_mnp_is_univ: \<open>M' \<union> N' = UNIV\<close>
        {
      assume \<open>M' \<inter> N' \<noteq> {}\<close>
      then have \<open>M' \<Turnstile>s N'\<close>
        using sound_cons.entails_reflexive sound_cons.entails_subsets
        by (meson Int_lower1 Int_lower2 sound_cons.entails_cond_reflexive)
          }
      moreover {
      assume empty_inter_mp_np: \<open>M' \<inter> N' = {}\<close>
        define Jpos where \<open>Jpos = {v. to_V (fml_ext v) \<in> M' \<and> is_Pos v}\<close>
          (* /!\ Jneg is empty because of sign preservation of fml_ext. Find correct definition! /!\ *)
        define Jneg where \<open>Jneg = {v |v. to_V (fml_ext v) \<in> N' \<and> \<not> is_Pos v}\<close>
        define Jstrip where \<open>Jstrip = Jpos \<union> Jneg\<close>
        have \<open>is_interpretation Jstrip\<close>
          unfolding is_interpretation_def 
        proof (clarsimp, rule ccontr)
          fix v1 v2
          assume v1_in: \<open>v1 \<in> Jstrip\<close> and
            v2_in: \<open>v2 \<in> Jstrip\<close> and
            v12_eq: \<open>to_V v1 = to_V v2\<close> and
            contra: \<open>is_Pos v1 \<noteq> is_Pos v2\<close>
          have pos_neg_cases: \<open>(v1 \<in> Jpos \<and> v2 \<in> Jneg) \<or> (v1 \<in> Jneg \<and> v2 \<in> Jpos)\<close>
            using v1_in v2_in contra unfolding Jstrip_def Jpos_def Jneg_def by force 
          then have \<open>to_V (fml_ext v1) \<noteq> to_V (fml_ext v2)\<close>
            using empty_inter_mp_np unfolding Jneg_def Jpos_def by auto 
          then show \<open>False\<close>
            using fml_ext_preserves_val[OF v12_eq] by blast 
        qed
        then obtain Jinterp where \<open>Jinterp = interp_of Jstrip\<close> by simp
        have \<open>total Jinterp\<close> unfolding total_def
        proof (intro allI)
          fix v::"'v neg"
            {
          assume \<open>to_V (fml_ext v) \<in> M'\<close>
          then have \<open>(Pos (to_V (fml_ext v))) \<in> fml_ext ` Jpos\<close>
            unfolding Jpos_def 
            sorry
            }
          obtain v\<^sub>J where \<open>to_V v\<^sub>J = v\<close>
            by (meson to_V.simps(1)) 
          then have \<open>v\<^sub>J \<in> Jpos \<or> v\<^sub>J \<in> Jneg\<close>
            using union_mnp_is_univ unfolding Jpos_def Jneg_def sorry
          show \<open>\<exists>v\<^sub>J. v\<^sub>J \<in>\<^sub>J Jinterp \<and> to_V v\<^sub>J = v\<close>
            sorry
        qed
      define J where \<open>J = total_interp_of ({v. fml_ext v \<in> Pos ` M'} \<union> {Neg v |v. fml_ext v \<notin> Pos ` M'})\<close>
        (* why can I define J above without proving that UNIV is covered? This shouldn't work! *)
      then have \<open>(fml_ext ` total_strip J) \<union> (Pos ` M) \<union> (Neg ` Pos ` N) \<subseteq> (Pos ` M') \<union> (Neg ` Pos ` N')\<close>

        sorry
      have \<open>M' \<Turnstile>s N'\<close>
        sorry
          }
      ultimately show \<open>M' \<Turnstile>s N'\<close>
        by auto 
    qed
    have \<open>M \<Turnstile>s N\<close>
      using sound_cons.entails_supsets[OF all_bigger_entail] .
      }
  ultimately show \<open>(to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N) \<equiv> (M \<Turnstile>s N)\<close>
    sorry
qed





































  (* Splitting report Lemma 5, 2/2 *)
lemma \<open>(to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N) \<equiv> (M \<Turnstile>s N)\<close>
proof -
  fix M N
    {
  assume \<open>to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N\<close>
  then have \<open> \<forall>J. (\<exists>M' N'. finite M' \<and> finite N' \<and>
    M' \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` M \<and> is_Pos C} \<and>
    N' \<subseteq> N \<union>
    {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` M \<and> \<not> is_Pos C} \<and>
    M' \<Turnstile>s N')\<close>
    using entails_sound_compact unfolding AF_entails_sound_def sound_cons.entails_neg_def
    by (simp, meson)
  moreover have \<open>\<forall>J. {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` M \<and> is_Pos C} =
    {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> {to_V C |C. C \<in> Pos ` M \<and> is_Pos C}\<close>
    by blast
  moreover have \<open>\<forall>J. {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` M \<and> \<not> is_Pos C} =
    {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} \<union> {to_V C |C. C \<in> Pos ` M \<and> \<not> is_Pos C}\<close>
    by blast
  ultimately have finite_sound_entails_m'_n': \<open>\<forall>J. (\<exists>M' N'. finite M' \<and> finite N' \<and>
    M' \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> M \<and>
    N' \<subseteq> N \<union> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} \<and>
    M' \<Turnstile>s N')\<close>
    by auto 
  have finite_sound_entails_m'_n'_jpos_jneg:
    \<open>\<forall>J. \<exists>fml_Jpos fml_Jneg M' N'. finite fml_Jpos \<and> finite fml_Jneg \<and> finite M' \<and> finite N' \<and>
    M' \<subseteq> M \<and> N' \<subseteq> N \<and> fml_Jpos \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<and>
    fml_Jneg \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} \<and>
    fml_Jpos \<union> M' \<Turnstile>s fml_Jneg \<union> N'\<close>
  proof
    fix J
    obtain M' N' where finite_m': "finite M'" and finite_n': "finite N'" and
      m'_sub: "M' \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> M" and
      n'_sub: "N' \<subseteq> N \<union> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C}" and
      m'_entails_n': "M' \<Turnstile>s N'"
      using finite_sound_entails_m'_n' by meson
    obtain M1 fml_Jpos where m'_split: "M1 \<union> fml_Jpos = M'" and m1_sub: "M1 \<subseteq> M" and
      j1_sub: "fml_Jpos \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C}"
      using m'_sub by (smt (z3) Un_commute subset_UnE) 
    have finite_m1_j1: "finite M1" "finite fml_Jpos"
      using m'_split finite_m' by auto
    obtain N1 fml_Jneg where n'_split: "N1 \<union> fml_Jneg = N'" and n1_sub: "N1 \<subseteq> N" and
      j2_sub: "fml_Jneg \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C}"
      using n'_sub by (smt (z3) Un_commute subset_UnE) 
    have finite_n1_j2: "finite N1" "finite fml_Jneg"
      using n'_split finite_n' by auto 
    have unions_entail: \<open>M1 \<union> fml_Jpos \<Turnstile>s N1 \<union> fml_Jneg\<close>
      using m'_entails_n' m'_split n'_split
      by metis
    show \<open>\<exists>fml_Jpos fml_Jneg M' N'. finite fml_Jpos \<and> finite fml_Jneg \<and> finite M' \<and> finite N' \<and>
      M' \<subseteq> M \<and> N' \<subseteq> N \<and> fml_Jpos \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<and>
      fml_Jneg \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} \<and>
      fml_Jpos \<union> M' \<Turnstile>s fml_Jneg \<union> N'\<close>
      using finite_m1_j1 finite_n1_j2 m1_sub n1_sub j1_sub j2_sub unions_entail 
      by (smt (verit, best) Un_commute) 
   qed   
   have finite_sound_entail_fml_j_pos_neg:
     \<open>\<forall>J. \<exists>fml_Jpos fml_Jneg. finite fml_Jpos \<and> finite fml_Jneg \<and>
     fml_Jpos \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<and>
     fml_Jneg \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} \<and>
     fml_Jpos \<union> M \<Turnstile>s fml_Jneg \<union> N\<close>
   proof
     fix J
     obtain M' N' fml_Jpos fml_Jneg where finite_jpos: "finite fml_Jpos" and
       finite_jneg: "finite fml_Jneg" and "finite M'" and "finite N'" and m'_subs:"M' \<subseteq> M" and
       n'_subs:"N' \<subseteq> N" and
       jpos_subs: "fml_Jpos \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C}" and
       jneg_subs: "fml_Jneg \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C}" and
       sound_entails:"fml_Jpos \<union> M' \<Turnstile>s fml_Jneg \<union> N'"
       using finite_sound_entails_m'_n'_jpos_jneg by meson
     have \<open>fml_Jpos \<union> M \<Turnstile>s fml_Jneg \<union> N\<close>
       using sound_cons.entails_subsets m'_subs n'_subs sound_entails by (meson Un_mono subset_refl) 
     then show \<open>\<exists>fml_Jpos fml_Jneg. finite fml_Jpos \<and> finite fml_Jneg \<and> 
       fml_Jpos \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<and>
       fml_Jneg \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} \<and>
       fml_Jpos \<union> M \<Turnstile>s fml_Jneg \<union> N\<close>
       using finite_jpos finite_jneg jpos_subs jneg_subs 
       by blast
   qed 
   have finite_sound_entail_fml_j:
     \<open>\<forall>J. \<exists>fml_Jfin. finite fml_Jfin \<and> fml_Jfin \<subseteq> fml_ext ` total_strip J \<and>
     {to_V C |C. C \<in> fml_Jfin \<and> is_Pos C} \<union> M \<Turnstile>s {to_V C |C. C \<in> fml_Jfin \<and> \<not> is_Pos C} \<union> N\<close>
   proof
     fix J
     obtain toV_Jpos toV_Jneg where fin_vpos: "finite toV_Jpos" and fin_vneg: "finite toV_Jneg" and
       jpos_subs: "toV_Jpos \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C}" and
       jneg_subs: "toV_Jneg \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C}" and
       pos_entails_neg: "toV_Jpos \<union> M \<Turnstile>s toV_Jneg \<union> N"
       using finite_sound_entail_fml_j_pos_neg by meson 
     have \<open>\<exists>Jpos\<subseteq>fml_ext ` total_strip J. finite Jpos \<and> toV_Jpos = to_V ` Jpos \<and>
       (\<forall>C\<in>Jpos. is_Pos C)\<close>
       using finite_subset_image_with_prop[OF fin_vpos,
         of "\<lambda>x. to_V x"  "fml_ext ` total_strip J" is_Pos, OF jpos_subs]
       by blast 
     then obtain Jpos where fpos_subs: \<open>Jpos \<subseteq> fml_ext ` total_strip J\<close> and
       fin_fpos: \<open>finite Jpos\<close> and v_to_f_pos: \<open>toV_Jpos = to_V ` Jpos\<close> and
       pos_all_pos: \<open>\<forall>C\<in>Jpos. is_Pos C\<close>
       by blast
     have \<open>\<exists>Jneg\<subseteq>fml_ext ` total_strip J. finite Jneg \<and> toV_Jneg = to_V ` Jneg \<and>
       (\<forall>C\<in>Jneg. \<not> is_Pos C)\<close>
       using finite_subset_image_with_prop[OF fin_vneg,
         of "\<lambda>x. to_V x"  "fml_ext ` total_strip J" "\<lambda>x. \<not> is_Pos x", OF jneg_subs]
       by blast 
     then obtain Jneg where fneg_subs: \<open>Jneg \<subseteq> fml_ext ` total_strip J\<close> and
       fin_fneg: \<open>finite Jneg\<close> and v_to_f_neg: \<open>toV_Jneg = to_V ` Jneg\<close> and
       neg_all_neg: \<open>\<forall>C\<in>Jneg. \<not> is_Pos C\<close>
       by blast
     define fml_Jfin where "fml_Jfin = Jpos \<union> Jneg"
     have \<open>{to_V C |C. C \<in> fml_Jfin \<and> is_Pos C} = to_V ` Jpos\<close>
       using pos_all_pos neg_all_neg unfolding fml_Jfin_def by blast 
     moreover have \<open>{to_V C |C. C \<in> fml_Jfin \<and> \<not> is_Pos C} = to_V ` Jneg\<close>
       using pos_all_pos neg_all_neg unfolding fml_Jfin_def by blast 
     moreover have \<open>finite fml_Jfin\<close> using fin_fneg fin_fpos unfolding fml_Jfin_def by blast 
     moreover have \<open>fml_Jfin \<subseteq> fml_ext ` total_strip J\<close>
       using fneg_subs fpos_subs unfolding fml_Jfin_def by blast 
     ultimately show \<open>\<exists>fml_Jfin. finite fml_Jfin \<and> fml_Jfin \<subseteq> fml_ext ` total_strip J \<and>
       {to_V C |C. C \<in> fml_Jfin \<and> is_Pos C} \<union> M \<Turnstile>s {to_V C |C. C \<in> fml_Jfin \<and> \<not> is_Pos C} \<union> N\<close>
       using pos_entails_neg v_to_f_pos v_to_f_neg
       by fastforce
   qed
   have \<open>\<forall>J. \<exists>Jfin. finite Jfin \<and> Jfin \<subseteq> total_strip J \<and>
     {to_V C |C. C \<in> fml_ext ` Jfin \<and> is_Pos C} \<union> M \<Turnstile>s
       {to_V C |C. C \<in> fml_ext ` Jfin \<and> \<not> is_Pos C} \<union> N\<close>
   proof
     fix J
     obtain fml_Jfin where "finite fml_Jfin" and "fml_Jfin \<subseteq> fml_ext ` total_strip J" and
       fml_sound_entails: "{to_V C |C. C \<in> fml_Jfin \<and> is_Pos C} \<union> M \<Turnstile>s
         {to_V C |C. C \<in> fml_Jfin \<and> \<not> is_Pos C} \<union> N"
       using finite_sound_entail_fml_j by blast
     then have \<open>\<exists>Jfin. finite Jfin \<and> Jfin \<subseteq> total_strip J \<and> fml_ext ` Jfin = fml_Jfin\<close>
       by (metis (no_types, opaque_lifting) finite_subset_image)
     then obtain Jfin where "finite Jfin" and "Jfin \<subseteq> total_strip J" and
       fml_jfin_is: "fml_ext ` Jfin = fml_Jfin"
       by blast
     moreover have \<open>{to_V C |C. C \<in> fml_ext ` Jfin \<and> is_Pos C} \<union> M \<Turnstile>s
       {to_V C |C. C \<in> fml_ext ` Jfin \<and> \<not> is_Pos C} \<union> N\<close>
       using fml_sound_entails fml_jfin_is by blast
     ultimately show \<open>\<exists>Jfin. finite Jfin \<and> Jfin \<subseteq> total_strip J \<and>
       {to_V C |C. C \<in> fml_ext ` Jfin \<and> is_Pos C} \<union> M \<Turnstile>s
         {to_V C |C. C \<in> fml_ext ` Jfin \<and> \<not> is_Pos C} \<union> N\<close>
       by blast 
   qed
   then obtain to_Jfin :: "'v total_interpretation \<Rightarrow> 'v neg set" where
     fin_to_Jfin: "finite (to_Jfin J)" and "(to_Jfin J) \<subseteq> total_strip J" and
     "{to_V C |C. C \<in> fml_ext ` (to_Jfin J) \<and> is_Pos C} \<union> M \<Turnstile>s
       {to_V C |C. C \<in> fml_ext ` (to_Jfin J) \<and> \<not> is_Pos C} \<union> N" for J
     by meson
   define Vfin :: "'v set" where "Vfin = to_V ` (\<Union>J. to_Jfin J)"
   have \<open>finite Vfin\<close>
   proof -
     have \<open>finite  (\<Union>J. to_Jfin J)\<close>
       using fin_to_Jfin sorry (* /!\ I suspect this does not hold /!\ *)
     have \<open>\<forall>J. finite (to_V ` (to_Jfin J))\<close>
     proof
       fix J
       show \<open>finite (to_V ` (to_Jfin J))\<close>
         using finite_imageI[OF fin_to_Jfin, of to_V] by blast
     qed
           
     
      find_theorems finite "\<Union>_. _" 


oops

 (*   have \<open>\<forall>J. \<exists>Jfin. finite (strip Jfin) \<and>
 *      strip Jfin \<subseteq> total_strip J \<and>
 *      {to_V C |C. C \<in> fml_ext ` strip Jfin \<and> is_Pos C} \<union> M \<Turnstile>s
 *        {to_V C |C. C \<in> fml_ext ` strip Jfin \<and> \<not> is_Pos C} \<union> N\<close>
 *    proof
 *      fix J
 *          find_theorems "total_strip _"
 *      obtain Jfin where "{to_V C |C. C \<in> fml_ext ` strip Jfin} = fml_Jpos \<union> fml_Jneg"
 * sorry
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 *    have \<open>\<exists>V. finite V \<and> (\<forall>J. \<exists>Jfin. finite (strip Jfin) \<and>
 *      strip Jfin \<subseteq> total_strip J \<and>
 *      {to_V C |C. C \<in> fml_ext ` strip Jfin \<and> is_Pos C} \<union> M \<Turnstile>s
 *        {to_V C |C. C \<in> fml_ext ` strip Jfin \<and> \<not> is_Pos C} \<union> N \<and>
 *      TODO)\<close>
 * 
 *      
 *      sorry *)



(*   then have \<open>\<exists>J's\<subseteq>total_strip J. finite J's \<and>
 *     {to_V C |C. (C \<in> fml_ext ` J's \<or> C \<in> Pos ` M) \<and> is_Pos C} \<union>
 *     {to_V C |C. C \<in> Pos ` N \<and> \<not> is_Pos C} \<Turnstile>s
 *       {to_V C |C. C \<in> Pos ` N \<and> is_Pos C} \<union>
 *       {to_V C |C. (C \<in> fml_ext ` J's \<or> C \<in> Pos ` M) \<and> \<not> is_Pos C} \<close>
 *     using entails_sound_compact unfolding AF_entails_sound_def sound_cons.entails_neg_def
 *     sorry
 *   have \<open>M \<Turnstile>s N\<close>
 *     unfolding AF_entails_def
 *     sorry
 *       }
 *   moreover {
 *   assume m_to_n: \<open>M \<Turnstile>s N\<close>
 *   have \<open>to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N\<close>
 *     unfolding AF_entails_sound_def sound_cons.entails_neg_def 
 *   proof (simp, rule allI)
 *     fix J
 *     have \<open>M \<subseteq> {to_V C |C. (C \<in> fml_ext ` total_strip J \<or> C \<in> Pos ` M) \<and> is_Pos C}\<close>
 *       by force
 *     then show \<open>{to_V C |C. (C \<in> fml_ext ` total_strip J \<or> C \<in> Pos ` M) \<and> is_Pos C} \<Turnstile>s
 *         N \<union> {to_V C |C. (C \<in> fml_ext ` total_strip J \<or> C \<in> Pos ` M) \<and> \<not> is_Pos C}\<close>
 *       using m_to_n by (meson sound_cons.entails_subsets sup.cobounded1)
 *   qed
 *       }
 *   ultimately show \<open>to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N \<equiv> M \<Turnstile>s N\<close>
 *     by argo
 * qed *)

 *)
