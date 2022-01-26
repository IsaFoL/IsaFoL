(* Title:        Extension of the lazy_given_clause locale from Saturation_Framework
 * Author:       Qi Qiu, 2021
 * Maintainer:   Sophie Tourret <stourret at loria.fr>, 2021 *)

section \<open>6 basic operations covered by lazy_given_clause.process rule\<close>

theory More_Lazy_Given_Clause
  imports
    More_Given_Clause_Basis
    Saturation_Framework.Given_Clause_Architectures
begin (* theory *)

context lazy_given_clause
begin (* context lazy_given_clause *)

subsection \<open>abbreviation, definition , type etc.\<close>

subsection \<open>6 basic operations\<close>

  lemma P0' :
    assumes "(C,l) \<in> Red_F \<N>" 
    shows "(T, \<N> \<union> {(C,l)}) \<leadsto>LGC (T, \<N>)"
  proof-
    have "{(C,l)} \<subseteq> Red_F (\<N> \<union> \<emptyset>)"
      using assms by simp
    moreover have "active_subset \<emptyset> = \<emptyset>" 
      using active_subset_def by simp
    ultimately show "(T, \<N> \<union> {(C,l)}) \<leadsto>LGC (T, \<N>)"
      by (metis process sup_bot_right) 
  qed

  lemma P1' : 
    assumes " C \<in> no_labels.Red_F (fst ` \<N>)"
    shows   "(T, \<N> \<union> {(C,l::'l)}) \<leadsto>LGC (T, \<N>)"
  proof-
    have "(C,l) \<in> Red_F \<N>" 
      using lemma59point1 assms by simp
    then show "(T, \<N> \<union> {(C,l::'l)}) \<leadsto>LGC (T, \<N>)" 
      using P0' by auto
  qed

  lemma P2' : 
    assumes "l \<noteq> active"
    shows   "(T, \<N>) \<leadsto>LGC (T, \<N> \<union> {(C,l)})"
  proof-
    have active_subset_C_l : "active_subset {(C,l)} = \<emptyset>" 
      using active_subset_def assms by simp
    also have "\<emptyset> \<subseteq> Red_F (\<N> \<union> {(C,l)})" 
      by simp
    finally show "(T, \<N>) \<leadsto>LGC (T, \<N> \<union> {(C,l)})"
      by (metis active_subset_C_l process sup_bot.right_neutral)
  qed

  lemma P3' : 
    assumes "(C',l') \<in> \<N>" and 
            "C' \<prec>\<cdot> C"
    shows "(T, \<N> \<union> {(C,l)}) \<leadsto>LGC (T, \<N>)"
  proof-
    have " C' \<in> fst ` \<N> "
      by (metis assms(1) fst_conv rev_image_eqI)
    then have "{(C,l)} \<subseteq> Red_F (\<N>)"
      using assms lemma59point2 by auto
    then show ?thesis 
      using P0' by simp
  qed


  lemma P4' : 
    assumes "(C',l') \<in> \<N>" and
            "l' \<sqsubset>L l" and
            "C' \<preceq>\<cdot> C"
    shows   "(T, \<N> \<union> {(C,l)}) \<leadsto>LGC (T, \<N>)"
  proof-
    have " (C,l) \<in> Red_F \<N> "
      using assms lemma59point3 by auto
    then show "(T, \<N> \<union> {(C,l)}) \<leadsto>LGC (T, \<N>)" 
      using P0' by auto
  qed

  lemma P5' : 
    assumes "l' \<sqsubset>L l" and
            "l' \<noteq> active"
    shows   "(T, \<N> \<union> {(C,l)}) \<leadsto>LGC (T, \<N> \<union> {(C,l')})"
  proof-
    have active_subset_c_l' : "active_subset {(C,l')} = \<emptyset>" 
      using active_subset_def assms by auto
    
    have "C \<doteq> C "
      by (simp add: equiv_equiv_F equivp_reflp)
    moreover have "(C,l') \<in> \<N> \<union> {(C,l')} "
      by auto
    ultimately have "(C,l) \<in> Red_F (\<N> \<union> {(C,l')})"
      using assms lemma59point3[of _ _ "\<N> \<union> {(C,l')}"] by auto
    then have "{(C,l)} \<subseteq> Red_F (\<N> \<union> {(C,l')})" 
      by auto

    then show "(T, \<N> \<union> {(C,l)}) \<leadsto>LGC (T, \<N> \<union> {(C,l')})"
      using active_subset_c_l' process[of _ _ "{(C,l)}" _ "{(C,l')}"] by auto
  qed

end(* context lazy_given_clause *)

end (* theory *)
