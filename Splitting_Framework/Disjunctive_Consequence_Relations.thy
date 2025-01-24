(* Title:        Formalizing an abstract calculus based on splitting in a modular way
 * Author:       Sophie Tourret <stourret at inria.fr>, 2020-2025
 *               Florent Krasnopol <florent.krasnopol at ens-paris-saclay.fr>, 2022
 *               Ghilain Bergeron <ghilain.bergeron at inria.fr>, 2023 *)

theory Disjunctive_Consequence_Relations
  imports Saturation_Framework.Calculus
    Propositional_Proof_Systems.Compactness
    "HOL-Library.Library"
    "HOL-Library.Product_Lexorder"
    Lazy_List_Limsup
    FSet_Extra
begin

section \<open>Disjunctive Consequence Relations\<close>

no_notation Sema.formula_semantics (infix "\<Turnstile>" 51)

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

 (* Unifying Splitting Lemma 5 *) 
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
end

section \<open>Extension to Negated Formulas\<close>

(* formalizing negated formulas uncovered a mistake in the corresponding paper-definition
  (sect. 2.1) *)

(* old def of sign datatype, that causes *a lot* of trouble *)
  (* datatype 'a neg = Pos "'a" | Neg "'a neg" *)
(* ("\<sim>_" 55) (*| Pos (nval_of: "'a neg") *) term "\<sim>F" *)

datatype 'a sign = Pos "'a" | Neg "'a"

instance sign :: (countable) countable
  by (rule countable_classI [of "(\<lambda>x. case x of Pos x \<Rightarrow> to_nat (True, to_nat x)
                                                  | Neg x \<Rightarrow> to_nat (False, to_nat x))"])
     (smt (verit, best) Pair_inject from_nat_to_nat sign.exhaust sign.simps(5) sign.simps(6))

fun neg :: \<open>'a sign \<Rightarrow> 'a sign\<close> where
  \<open>neg (Pos C) = Neg C\<close> |
  \<open>neg (Neg C) = Pos C\<close>

fun to_V :: "'a sign \<Rightarrow> 'a" where
  "to_V (Pos C) = C" |
  "to_V (Neg C) = C"

lemma neg_neg_A_is_A [simp]: \<open>neg (neg A) = A\<close>
  by (metis neg.simps(1) neg.simps(2) to_V.elims)

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

context consequence_relation
begin
definition entails_neg :: "'f sign set \<Rightarrow> 'f sign set \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<sim>" 50) where
  "entails_neg M N \<equiv> {C. Pos C \<in> M} \<union> {C. Neg C \<in> N} \<Turnstile> {C. Pos C \<in> N} \<union> {C. Neg C \<in> M}"

lemma swap_neg_in_entails_neg: \<open>{neg A} \<Turnstile>\<^sub>\<sim> {neg B} \<longleftrightarrow> {B} \<Turnstile>\<^sub>\<sim> {A}\<close>
  unfolding entails_neg_def
  by (smt (verit, ccfv_threshold) Collect_cong Un_commute mem_Collect_eq neg.simps(1)
       neg_neg_A_is_A singleton_conv2)

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

lemma entails_of_entails_iff: 
  \<open>{C} \<Turnstile>\<^sub>\<sim> Cs \<Longrightarrow> finite Cs \<Longrightarrow> card Cs \<ge> 1 \<Longrightarrow>
    (\<forall> C\<^sub>i \<in> Cs. \<M> \<union> {C\<^sub>i} \<Turnstile>\<^sub>\<sim> {Pos bot}) \<Longrightarrow> \<M> \<union> {C} \<Turnstile>\<^sub>\<sim> {Pos bot}\<close>
proof -
  assume \<open>{C} \<Turnstile>\<^sub>\<sim> Cs\<close> and
         finite_Cs: \<open>finite Cs\<close> and
         Cs_not_empty: \<open>card Cs \<ge> 1\<close> and
         all_C\<^sub>i_entail_bot: \<open>\<forall> C\<^sub>i \<in> Cs. \<M> \<union> {C\<^sub>i} \<Turnstile>\<^sub>\<sim> {Pos bot}\<close>
  then have \<open>\<M> \<union> {C} \<Turnstile>\<^sub>\<sim> Cs\<close>
    using Un_upper2 consequence_relation.entails_subsets subsetI
    by (metis neg_ext_cons_rel.entails_subsets)
  then show \<open>\<M> \<union> {C} \<Turnstile>\<^sub>\<sim> {Pos bot}\<close>
    using Cs_not_empty all_C\<^sub>i_entail_bot
  proof (induct rule: finite_ne_induct[OF finite_Cs])
    case 1
    then show ?case
      using Cs_not_empty
      by force
  next
    case (2 x)
    then show ?case
      using consequence_relation.entails_cut ext_cons_rel
      by fastforce
  next
    case insert: (3 x F)

    have card_F_ge_1: \<open>card F \<ge> 1\<close>
      by (meson card_0_eq insert.hyps(1) insert.hyps(2) less_one linorder_not_less)

    have \<open>\<M> \<union> {C} \<Turnstile>\<^sub>\<sim> {Pos bot, x} \<union> F\<close>
      by (smt (verit, ccfv_threshold) Un_insert_left Un_insert_right Un_upper2
          consequence_relation.entails_subsets insert.prems(1) insert_is_Un ext_cons_rel)
    then have \<open>\<M> \<union> {C} \<Turnstile>\<^sub>\<sim> {Pos bot} \<union> {x} \<union> F\<close>
      by (metis insert_is_Un)
    moreover have \<open>\<M> \<union> {C} \<union> {x} \<Turnstile>\<^sub>\<sim> {Pos bot} \<union> F\<close>
      by (smt (verit, ccfv_SIG) Un_upper2 consequence_relation.entails_subsets insert.prems(3)
          insertCI ext_cons_rel sup_assoc sup_ge1 sup_left_commute)
    ultimately have \<open>\<M> \<union> {C} \<Turnstile>\<^sub>\<sim> {Pos bot} \<union> F\<close>
      using consequence_relation.entails_cut ext_cons_rel
      by fastforce
    then have \<open>\<M> \<union> {C} \<Turnstile>\<^sub>\<sim> F\<close>
      using consequence_relation.bot_entails_empty consequence_relation.entails_cut ext_cons_rel
      by fastforce
    then show ?case
      using insert card_F_ge_1
      by blast
  qed
qed

end

end