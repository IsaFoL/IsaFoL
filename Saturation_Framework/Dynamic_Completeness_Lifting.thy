(*  Title:       Dynamic_Completeness_Lifting
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018
*)

section \<open>Adding a family of well-founded orderings to the standard lifting\<close>

(* TODO: rename file and theory to something that reflects its content better *)
theory Dynamic_Completeness_Lifting
  imports
    Saturation_Framework_Preliminaries
    Well_Quasi_Orders.Minimal_Elements
begin

locale lifting_with_wf_ordering_family = standard_lifting Bot_F Inf_F Bot_G Inf_G entails_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf
  for
    Bot_F :: \<open>'f set\<close> and
    Inf_F :: \<open>'f inference set\<close> and
    Bot_G :: \<open>'g set\<close> and
    entails_G :: \<open>'g set \<Rightarrow> 'g set \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    Inf_G :: \<open>'g inference set\<close> and
    Red_Inf_G :: \<open>'g set \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g set \<Rightarrow> 'g set\<close> and
    \<G>_F :: "'f \<Rightarrow> 'g set" and
    \<G>_Inf :: "'f inference \<Rightarrow> 'g inference set"
  + fixes
    Prec_F_g :: \<open>'g \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool\<close>
  assumes
    all_wf: "minimal_element (Prec_F_g g) UNIV"
begin

definition Red_Inf_\<G> :: "'f set \<Rightarrow> 'f inference set" where
  \<open>Red_Inf_\<G> N = {\<iota> \<in> Inf_F. \<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_set N)}\<close>

definition Red_F_\<G> :: "'f set \<Rightarrow> 'f set" where
  \<open>Red_F_\<G> N = {C. \<forall>D \<in> \<G>_F C. D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E \<in> N. Prec_F_g D E C \<and> D \<in> \<G>_F E)}\<close>

lemma Prec_trans: 
  assumes 
    \<open>Prec_F_g D A B\<close> and
    \<open>Prec_F_g D B C\<close>
  shows
    \<open>Prec_F_g D A C\<close>
  using minimal_element.po assms unfolding po_on_def transp_on_def by (smt UNIV_I all_wf)

lemma prop_nested_in_set: "D \<in> P C \<Longrightarrow> C \<in> {C. \<forall>D \<in> P C. A D \<or> B C D} \<Longrightarrow> A D \<or> B C D"
  by blast

text \<open>lemma 31 in the technical report\<close>
lemma Red_F_\<G>_equiv_def: 
  \<open>Red_F_\<G> N = {C. \<forall>Di \<in> \<G>_F C. Di \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E \<in> (N - Red_F_\<G> N). Prec_F_g Di E C \<and> Di \<in> \<G>_F E)}\<close>
proof (rule;clarsimp)
  fix C D
  assume 
    C_in: \<open>C \<in> Red_F_\<G> N\<close> and
    D_in: \<open>D \<in> \<G>_F C\<close> and
    not_sec_case: \<open>\<forall>E \<in> N - Red_F_\<G> N. Prec_F_g D E C \<longrightarrow> D \<notin> \<G>_F E\<close>
  have C_in_unfolded: "C \<in> {C. \<forall>Di \<in> \<G>_F C. Di \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E\<in>N. Prec_F_g Di E C \<and> Di \<in> \<G>_F E)}"
    using C_in unfolding Red_F_\<G>_def .
  have neg_not_sec_case: \<open>\<not> (\<exists>E\<in>N - Red_F_\<G> N. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close> using not_sec_case by clarsimp 
  have unfol_C_D: \<open>D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E\<in>N. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close> 
    using prop_nested_in_set[of D \<G>_F C "\<lambda>x. x \<in> Red_F_G (\<Union> (\<G>_F ` N))"
      "\<lambda>x y. \<exists>E \<in> N. Prec_F_g y E x \<and> y \<in> \<G>_F E", OF D_in C_in_unfolded] by blast
  show \<open>D \<in> Red_F_G (\<G>_set N)\<close> 
  proof (rule ccontr)
    assume contrad: \<open>D \<notin> Red_F_G (\<G>_set N)\<close>
    have non_empty: \<open>\<exists>E\<in>N. Prec_F_g D E C \<and> D \<in> \<G>_F E\<close> using contrad unfol_C_D by auto
    define B where \<open>B = {E \<in> N. Prec_F_g D E C \<and> D \<in> \<G>_F E}\<close>
    then have B_non_empty: \<open>B \<noteq> {}\<close> using non_empty by auto
    interpret minimal_element "Prec_F_g D" UNIV using all_wf[of D] .
    obtain F :: 'f where F: \<open>F = min_elt B\<close> by auto
    then have D_in_F: \<open>D \<in> \<G>_F F\<close> unfolding B_def using non_empty
      by (smt Sup_UNIV Sup_upper UNIV_I contra_subsetD empty_iff empty_subsetI mem_Collect_eq min_elt_mem unfol_C_D) 
    have F_prec: \<open>Prec_F_g D F C\<close> using F min_elt_mem[of B, OF _ B_non_empty] unfolding B_def by auto
    have F_not_in: \<open>F \<notin> Red_F_\<G> N\<close>
    proof
      assume F_in: \<open>F \<in> Red_F_\<G> N\<close>
      have unfol_F_D: \<open>D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>G\<in>N. Prec_F_g D G F \<and> D \<in> \<G>_F G)\<close>
        using F_in D_in_F unfolding Red_F_\<G>_def by auto
      then have \<open>\<exists>G\<in>N. Prec_F_g D G F \<and> D \<in> \<G>_F G\<close> using contrad D_in unfolding Red_F_\<G>_def by auto
      then obtain G where G_in: \<open>G \<in> N\<close> and G_prec: \<open>Prec_F_g D G F\<close> and G_map: \<open>D \<in> \<G>_F G\<close> by auto
      have \<open>Prec_F_g D G C\<close> using G_prec F_prec Prec_trans by blast
      then have \<open>G \<in> B\<close> unfolding B_def using G_in G_map by auto
      then show \<open>False\<close> using F G_prec min_elt_minimal[of B G, OF _ B_non_empty] by auto
    qed
    have \<open>F \<in> N\<close> using F by (metis B_def B_non_empty mem_Collect_eq min_elt_mem top_greatest)
    then have \<open>F \<in> N - Red_F_\<G> N\<close> using F_not_in by auto
    then show \<open>False\<close> 
      using D_in_F neg_not_sec_case F_prec by blast
  qed
next
  fix C
  assume only_if: \<open>\<forall>D\<in>\<G>_F C. D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E\<in>N - Red_F_\<G> N. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
  show \<open>C \<in> Red_F_\<G> N\<close> unfolding Red_F_\<G>_def using only_if by auto
qed

text \<open>lemma 32 in the technical report\<close>
lemma not_red_map_in_map_not_red: \<open>\<G>_set N - Red_F_G (\<G>_set N) \<subseteq> \<G>_set (N - Red_F_\<G> N)\<close>
proof
  fix D
  assume
    D_hyp: \<open>D \<in> \<G>_set N - Red_F_G (\<G>_set N)\<close>
  interpret minimal_element "Prec_F_g D" UNIV using all_wf[of D] .
  have D_in: \<open>D \<in> \<G>_set N\<close> using D_hyp by blast
  have  D_not_in: \<open>D \<notin> Red_F_G (\<G>_set N)\<close> using D_hyp by blast
  have exist_C: \<open>\<exists>C. C \<in> N \<and> D \<in> \<G>_F C\<close> using D_in by auto
  define B where \<open>B = {C \<in> N. D \<in> \<G>_F C}\<close>
  obtain C where C: \<open>C = min_elt B\<close> by auto
  have C_in_N: \<open>C \<in> N\<close> 
    using exist_C by (metis B_def C empty_iff mem_Collect_eq min_elt_mem top_greatest)
  have D_in_C: \<open>D \<in> \<G>_F C\<close> 
    using exist_C by (metis B_def C empty_iff mem_Collect_eq min_elt_mem top_greatest)
  have C_not_in: \<open>C \<notin> Red_F_\<G> N\<close>
  proof
    assume C_in: \<open>C \<in> Red_F_\<G> N\<close>
    have \<open>D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E\<in>N. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
      using C_in D_in_C unfolding Red_F_\<G>_def by auto
    then show \<open>False\<close>
      proof
        assume \<open>D \<in> Red_F_G (\<G>_set N)\<close>
        then show \<open>False\<close> using D_not_in by simp
      next
        assume \<open>\<exists>E\<in>N. Prec_F_g D E C \<and> D \<in> \<G>_F E\<close>
        then show \<open>False\<close> 
          using C by (metis (no_types, lifting) B_def UNIV_I empty_iff mem_Collect_eq 
              min_elt_minimal top_greatest)
      qed
  qed
  show \<open>D \<in> \<G>_set (N - Red_F_\<G> N)\<close> using D_in_C C_not_in C_in_N by blast
qed

text \<open>lemma 33 in the technical report\<close>
lemma Red_F_Bot_F: \<open>B \<in> Bot_F \<Longrightarrow> N \<Turnstile>\<G> {B} \<Longrightarrow> N - Red_F_\<G> N \<Turnstile>\<G> {B}\<close>
proof -
  fix B N
  assume
    B_in: \<open>B \<in> Bot_F\<close> and
    N_entails: \<open>N \<Turnstile>\<G> {B}\<close>
  then have to_bot: \<open>\<G>_set N - Red_F_G (\<G>_set N) \<Turnstile>G \<G>_F B\<close> 
    using Ground.Red_F_Bot Bot_map unfolding entails_\<G>_def 
      by (smt cSup_singleton Ground.entail_set_all_formulas image_insert image_is_empty subsetCE)
  have from_f: \<open>\<G>_set (N - Red_F_\<G> N) \<Turnstile>G \<G>_set N - Red_F_G (\<G>_set N)\<close>
    using Ground.subset_entailed[OF not_red_map_in_map_not_red] by blast
  then have \<open>\<G>_set (N - Red_F_\<G> N) \<Turnstile>G \<G>_F B\<close> using to_bot Ground.entails_trans by blast
  then show \<open>N - Red_F_\<G> N \<Turnstile>\<G> {B}\<close> using Bot_map unfolding entails_\<G>_def by simp
qed

text \<open>lemma 34 in the technical report 1/2\<close>
lemma Red_F_of_subset_F: \<open>N \<subseteq> N' \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> N'\<close>
  using Ground.Red_F_of_subset unfolding Red_F_\<G>_def by (smt Collect_mono \<G>_subset subset_iff)

text \<open>lemma 34 in the technical report 2/2\<close>
lemma Red_Inf_of_subset_F: \<open>N \<subseteq> N' \<Longrightarrow> Red_Inf_\<G> N \<subseteq> Red_Inf_\<G> N'\<close>
  using Ground.Red_Inf_of_subset unfolding Red_Inf_\<G>_def by (smt Collect_mono \<G>_subset subset_iff)

text \<open>lemma 35 in the technical report\<close>
lemma Red_F_of_Red_F_subset_F: \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> (N - N')\<close>
proof
  fix N N' C
  assume 
    N'_in_Red_F_N: \<open>N' \<subseteq> Red_F_\<G> N\<close> and
    C_in_red_F_N: \<open>C \<in> Red_F_\<G> N\<close>
  have lem8: \<open>\<forall>D \<in> \<G>_F C. D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E \<in> (N - Red_F_\<G> N). Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
    using Red_F_\<G>_equiv_def C_in_red_F_N by blast
  show \<open>C \<in> Red_F_\<G> (N - N')\<close> unfolding Red_F_\<G>_def
  proof (rule,rule)
    fix D
    assume \<open>D \<in> \<G>_F C\<close>
    then have \<open>D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E \<in> (N - Red_F_\<G> N). Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
      using lem8 by auto
    then show \<open>D \<in> Red_F_G (\<G>_set (N - N')) \<or> (\<exists>E\<in>N - N'. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
    proof
      assume \<open>D \<in> Red_F_G (\<G>_set N)\<close>
      then have \<open>D \<in> Red_F_G (\<G>_set N - Red_F_G (\<G>_set N))\<close>
        using Ground.Red_F_of_Red_F_subset[of "Red_F_G (\<G>_set N)" "\<G>_set N"] by auto
      then have \<open>D \<in> Red_F_G (\<G>_set (N - Red_F_\<G> N))\<close> 
        using Ground.Red_F_of_subset[OF not_red_map_in_map_not_red[of N]] by auto
      then have \<open>D \<in> Red_F_G (\<G>_set (N - N'))\<close>
        using N'_in_Red_F_N \<G>_subset[of "N - Red_F_\<G> N" "N - N'"]
        by (smt DiffE DiffI Ground.Red_F_of_subset subsetCE subsetI)
      then show ?thesis by blast
    next
      assume \<open>\<exists>E\<in>N - Red_F_\<G> N. Prec_F_g D E C \<and> D \<in> \<G>_F E\<close>
      then obtain E where 
        E_in: \<open>E\<in>N - Red_F_\<G> N\<close> and 
        E_prec_C: \<open>Prec_F_g D E C\<close> and 
        D_in: \<open>D \<in> \<G>_F E\<close> 
        by auto
      have \<open>E \<in> N - N'\<close> using E_in N'_in_Red_F_N by blast
      then show ?thesis using E_prec_C D_in by blast
    qed
  qed
qed

text \<open>lemma 36 in the technical report\<close>
lemma Red_Inf_of_Red_F_subset_F: \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_Inf_\<G> N \<subseteq> Red_Inf_\<G> (N - N') \<close>
proof
  fix N N' \<iota>
  assume
    N'_in_Red_F_N: \<open>N' \<subseteq> Red_F_\<G> N\<close> and
    i_in_Red_Inf_N: \<open>\<iota> \<in> Red_Inf_\<G> N\<close>
  have i_in: \<open>\<iota> \<in> Inf_F\<close> using i_in_Red_Inf_N unfolding Red_Inf_\<G>_def by blast
  have \<open>\<forall>\<iota>' \<in> \<G>_Inf \<iota>. \<iota>' \<in> Red_Inf_G (\<G>_set N)\<close> using i_in_Red_Inf_N unfolding Red_Inf_\<G>_def by fast
  then have \<open>\<forall>\<iota>' \<in> \<G>_Inf \<iota>. \<iota>' \<in> Red_Inf_G (\<G>_set N - Red_F_G (\<G>_set N))\<close> 
    using Ground.Red_Inf_of_Red_F_subset by blast
  then have \<open>\<forall>\<iota>' \<in> \<G>_Inf \<iota>. \<iota>' \<in> Red_Inf_G (\<G>_set (N - Red_F_\<G> N))\<close>
    using Ground.Red_Inf_of_subset[OF not_red_map_in_map_not_red[of N]] by auto
  then have \<open>\<forall>\<iota>' \<in> \<G>_Inf \<iota>. \<iota>' \<in> Red_Inf_G (\<G>_set (N - N'))\<close> using  N'_in_Red_F_N 
      proof - (*proof suggested by sledgehammer, used because the smt alternative timeouts*)
        have "(\<forall>F Fa f. \<not> F \<subseteq> Fa \<or> (f::'f) \<notin> F \<or> f \<in> Fa) = (\<forall>F Fa f. \<not> F \<subseteq> Fa \<or> (f::'f) \<notin> F \<or> f \<in> Fa)"
          by blast
        then have "N - Red_F_\<G> N \<subseteq> N - N'" using \<open>N' \<subseteq> Red_F_\<G> N\<close> by blast  then show ?thesis
          by (meson \<G>_subset \<open>\<forall>\<iota>'\<in>\<G>_Inf \<iota>. \<iota>' \<in> Red_Inf_G (\<G>_set (N - Red_F_\<G> N))\<close> calculus_with_red_crit.Red_Inf_of_subset standard_lifting_axioms standard_lifting_def subsetCE)
      qed
  then show \<open>\<iota> \<in> Red_Inf_\<G> (N - N')\<close> unfolding Red_Inf_\<G>_def using i_in by blast
qed

text \<open>lemma 37 in the technical report\<close>
lemma Red_Inf_of_Inf_to_N_F: 
  assumes
    i_in: \<open>\<iota> \<in> Inf_F\<close> and
    concl_i_in: \<open>concl_of \<iota> \<in> N\<close>
  shows
    \<open>\<iota> \<in> Red_Inf_\<G> N \<close>
proof -
  have \<open>\<iota> \<in> Inf_F \<Longrightarrow> \<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_F (concl_of \<iota>))\<close> using inf_map by simp
  moreover have \<open>Red_Inf_G (\<G>_F (concl_of \<iota>)) \<subseteq> Red_Inf_G (\<G>_set N)\<close>
    using concl_i_in Ground.Red_Inf_of_subset by blast
  ultimately show ?thesis using i_in unfolding Red_Inf_\<G>_def by simp
qed

text \<open>theorem 38 in the technical report\<close>
sublocale lifted_calculus_with_red_crit: calculus_with_red_crit 
  where
    Bot = Bot_F and Inf = Inf_F and entails = entails_\<G> and
    Red_Inf = Red_Inf_\<G> and Red_F = Red_F_\<G>
proof
  fix B N N' \<iota>
  show \<open>Red_Inf_\<G> N \<subseteq> Inf_F\<close> unfolding Red_Inf_\<G>_def by blast
  show \<open>B \<in> Bot_F \<Longrightarrow> N \<Turnstile>\<G> {B} \<Longrightarrow> N - Red_F_\<G> N \<Turnstile>\<G> {B}\<close> using Red_F_Bot_F by simp
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> N'\<close> using Red_F_of_subset_F by simp
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_Inf_\<G> N \<subseteq> Red_Inf_\<G> N'\<close> using Red_Inf_of_subset_F by simp
  show \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> (N - N')\<close> using Red_F_of_Red_F_subset_F by simp
  show \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_Inf_\<G> N \<subseteq> Red_Inf_\<G> (N - N')\<close> using Red_Inf_of_Red_F_subset_F by simp
  show \<open>\<iota> \<in> Inf_F \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_Inf_\<G> N\<close> using Red_Inf_of_Inf_to_N_F by simp
qed

end


definition Empty_Order :: \<open>'f \<Rightarrow> 'f \<Rightarrow> bool\<close> where
  "Empty_Order C1 C2 \<equiv> False" 

locale lifting_equivalence_with_empty_order = any_order_lifting: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf Prec_F_g + empty_order_lifting: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf "\<lambda>g. Empty_Order"
  for
    \<G>_F :: \<open>'f \<Rightarrow> 'g set\<close> and
    \<G>_Inf :: \<open>'f inference \<Rightarrow> 'g inference set\<close> and
    Bot_F :: \<open>'f set\<close> and
    Inf_F :: \<open>'f inference set\<close> and
    Bot_G :: \<open>'g set\<close> and
    Inf_G :: \<open>'g inference set\<close> and
    entails_G :: \<open>'g set \<Rightarrow> 'g set \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    Red_Inf_G :: \<open>'g set \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g set \<Rightarrow> 'g set\<close> and
    Prec_F_g :: \<open>'g \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool\<close>

sublocale lifting_with_wf_ordering_family \<subseteq> lifting_equivalence_with_empty_order
proof
  show "po_on Empty_Order UNIV" unfolding Empty_Order_def po_on_def by (simp add: transp_onI wfp_on_imp_irreflp_on)
  show "wfp_on Empty_Order UNIV" unfolding wfp_on_def Empty_Order_def by simp
qed

context lifting_equivalence_with_empty_order
begin

text "lemma 39 from the technical report"
lemma "any_order_lifting.lifted_calculus_with_red_crit.saturated N = empty_order_lifting.lifted_calculus_with_red_crit.saturated N" by standard

text "lemma 40 from the technical report"
lemma static_empty_order_equiv_static: "static_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G> empty_order_lifting.Red_Inf_\<G> empty_order_lifting.Red_F_\<G> = static_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G> any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>"
  unfolding static_refutational_complete_calculus_def
  by (rule iffI) (standard,(standard)[],simp)+
   
text "theorem 41 from the technical report"
theorem "static_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G> empty_order_lifting.Red_Inf_\<G> empty_order_lifting.Red_F_\<G> = dynamic_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G> any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G> " (is "?static=?dynamic")
proof
  assume ?static
  then have static_general: "static_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G> any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>" (is "?static_gen") using static_empty_order_equiv_static by simp
  interpret static_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G> any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>
    using static_general .
  show "?dynamic" by standard 
next
  assume dynamic_gen: ?dynamic
  interpret dynamic_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G> any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>
    using dynamic_gen .
  have "static_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G> any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>"
    by standard
  then show "?static" using static_empty_order_equiv_static by simp
qed

end

subsection \<open>Intersection of Liftings\<close>


locale lifting_equivalence_with_red_crit_family = Non_ground: inference_system Inf_F
  + Ground_family: calculus_with_red_crit_family Bot_G Inf_G Q entails_q Red_Inf_q Red_F_q
  for
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    Inf_G :: \<open>'g inference set\<close> and
    Q :: "'q set" and
    entails_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g set \<Rightarrow> bool)" and
    Red_Inf_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g inference set)" and
    Red_F_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g set)"
  + fixes
    Bot_F :: "'f set" and
    \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set" and
    \<G>_Inf_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set" and
    Prec_F_g :: "'g \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool"
  assumes
    Q_not_empty: "Q \<noteq> {}" and
    standard_lifting_family: "q \<in> Q \<Longrightarrow> lifting_with_wf_ordering_family Bot_F Inf_F Bot_G (entails_q q) Inf_G (Red_Inf_q q) (Red_F_q q) (\<G>_F_q q) (\<G>_Inf_q q) Prec_F_g" 
begin

definition \<G>_set_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'g set" where
  "\<G>_set_q q N \<equiv> UNION N (\<G>_F_q q)"

definition Red_Inf_\<G>_Q :: "'f set \<Rightarrow> 'f inference set" where
  "Red_Inf_\<G>_Q N = (\<Inter>q\<in>Q. {\<iota> \<in> Inf_F. \<G>_Inf_q q \<iota> \<subseteq> Red_Inf_q q (\<G>_set_q q N)})"

definition Red_F_\<G>_empty :: "'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_empty N = (\<Inter>q\<in>Q. {C. \<forall>D \<in> \<G>_F_q q C. D \<in> Red_F_q q (\<G>_set_q q N) \<or> (\<exists>E \<in> N. Prec_F_g D E C \<and> D \<in> \<G>_F_q q E)})"

definition entails_\<G>_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> bool" where
  "entails_\<G>_q q N1 N2 \<equiv> entails_q q (\<G>_set_q q N1) (\<G>_set_q q N2)"

lemma \<open>consequence_relation_family Bot_F Q entails_\<G>_q\<close>
proof
  show \<open>Q \<noteq> {}\<close> by (rule Q_not_empty)
next
oops

definition entails_\<G>_Q :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" where
  "entails_\<G>_Q N1 N2 \<equiv> \<forall>q\<in>Q. entails_q q (\<G>_set_q q N1) (\<G>_set_q q N2)"


lemma "calculus_with_red_crit Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_empty"
proof
  show \<open>Bot_F \<noteq> {}\<close>
    using Q_not_empty standard_lifting_family
    by (meson ex_in_conv lifting_with_wf_ordering_family.axioms(1) standard_lifting.Bot_F_not_empty)
oops


end


subsection \<open>Adding labels\<close>

locale labeled_redundancy_criterion_lifting = redundancy_criterion_lifting \<G>_F \<G>_Inf Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G Prec_F
  for
    \<G>_F :: "'f \<Rightarrow> 'g set" and
    \<G>_Inf :: "'f inference \<Rightarrow> 'g inference set" and
    Bot_F :: "'f set" and
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    entails_G :: "'g set \<Rightarrow> 'g set \<Rightarrow> bool"  (infix "\<Turnstile>G" 50) and
    Inf_G :: "'g inference set" and
    Red_Inf_G :: "'g set \<Rightarrow> 'g inference set" and
    Red_F_G :: "'g set \<Rightarrow> 'g set" and
    Prec_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool"  (infix "\<sqsubset>" 50)
  + fixes
    l :: \<open>'l itself\<close> and
    Inf_FL :: \<open>('f \<times> 'l) inference set\<close>
  assumes
    Inf_F_to_Inf_FL: \<open>\<iota>\<^sub>F \<in> Inf_F \<Longrightarrow> length (Ll :: 'l list) = length (prems_of \<iota>\<^sub>F) \<Longrightarrow> \<exists>L0. Infer (zip (prems_of \<iota>\<^sub>F) Ll) (concl_of \<iota>\<^sub>F, L0) \<in> Inf_FL\<close> and
    Inf_FL_to_Inf_F: \<open>\<iota>\<^sub>F\<^sub>L \<in> Inf_FL \<Longrightarrow> Infer (map fst (prems_of \<iota>\<^sub>F\<^sub>L)) (fst (concl_of \<iota>\<^sub>F\<^sub>L)) \<in> Inf_F\<close>
begin

definition to_F :: \<open>('f \<times> 'l) inference \<Rightarrow> 'f inference\<close> where \<open>to_F \<iota>\<^sub>F\<^sub>L = Infer (map fst (prems_of \<iota>\<^sub>F\<^sub>L)) (fst (concl_of \<iota>\<^sub>F\<^sub>L))\<close>

text \<open>The set FL is implicitly defined as \<^term>\<open>UNIV::('f\<times>'l) set\<close> and the function \<^term>\<open>proj_1\<close> is implicitly defined as \<^term>\<open>(`) fst\<close>.\<close>
definition Bot_FL :: \<open>('f \<times> 'l) set\<close> where \<open>Bot_FL = Bot_F \<times> UNIV\<close>

definition \<G>_F_L :: \<open>('f \<times> 'l) \<Rightarrow> 'g set\<close> where \<open>\<G>_F_L CL = \<G>_F (fst CL)\<close>

definition \<G>_Inf_L :: \<open>('f \<times> 'l) inference \<Rightarrow> 'g inference set\<close> where \<open>\<G>_Inf_L \<iota>\<^sub>F\<^sub>L = \<G>_Inf (to_F \<iota>\<^sub>F\<^sub>L)\<close>

(* definition entails_sound_FL :: \<open>('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> bool\<close> (infix "|\<approx>FL" 50) where \<open>CL1 |\<approx>FL
CL2 \<equiv> fst ` CL1 |\<approx>F fst ` CL2\<close> *)

text \<open>Lemma 20 from the technical report\<close>
sublocale labeled_standard_lifting: standard_lifting
  where
    Bot_F = Bot_FL and
    Inf_F = Inf_FL and
    \<G>_F = \<G>_F_L and
    \<G>_Inf = \<G>_Inf_L
proof
  fix B NL
  show "Bot_FL \<noteq> {}" sorry
(* next
  fix NL1 NL2
  show "NL2 \<subseteq> NL1 \<Longrightarrow> NL1 |\<approx>FL NL2"
  proof -
    assume "NL2 \<subseteq> NL1"
    then have "fst ` NL2 \<subseteq> fst ` NL1" by (simp add: image_mono)
    then show "NL1 |\<approx>FL NL2" unfolding entails_sound_FL_def using Non_ground.subset_entailed by simp
  qed
next
  fix NL1 NL2
  show "\<forall>C\<in>NL2. NL1 |\<approx>FL {C} \<Longrightarrow> NL1 |\<approx>FL NL2" 
    unfolding entails_sound_FL_def using Non_ground.all_formulas_entailed
    by (smt image_empty image_iff image_insert)
next
  fix NL1 NL2 NL3
  show "NL1 |\<approx>FL NL2 \<Longrightarrow> NL2 |\<approx>FL NL3 \<Longrightarrow> NL1 |\<approx>FL NL3"
    unfolding entails_sound_FL_def using Non_ground.entails_trans by blast
next
  fix \<iota>
  show "\<iota> \<in> Inf_FL \<Longrightarrow> set (prems_of \<iota>) |\<approx>FL {concl_of \<iota>}"
    unfolding entails_sound_FL_def using Inf_FL_to_Inf_F Non_ground.soundness by force *)
next
  show "B\<in>Bot_FL \<Longrightarrow> \<G>_F_L B \<noteq> {}" for B
    unfolding \<G>_F_L_def Bot_FL_def using Bot_map_not_empty by auto
next
  show "B\<in>Bot_FL \<Longrightarrow> \<G>_F_L B \<subseteq> Bot_G" for B
    unfolding \<G>_F_L_def Bot_FL_def using Bot_map by force
next
  fix CL
  show "\<G>_F_L CL \<inter> Bot_G \<noteq> {} \<longrightarrow> CL \<in> Bot_FL"
    unfolding \<G>_F_L_def Bot_FL_def using Bot_cond by (metis SigmaE UNIV_I UNIV_Times_UNIV mem_Sigma_iff prod.sel(1))
next
  fix \<iota>
  assume \<open>\<iota> \<in> Inf_FL\<close>
  then show "\<G>_Inf_L \<iota> \<subseteq> Red_Inf_G (\<G>_F_L (concl_of \<iota>))"
    unfolding \<G>_Inf_L_def \<G>_F_L_def to_F_def using inf_map Inf_FL_to_Inf_F by fastforce
qed

definition Labeled_Empty_Order :: \<open> ('f \<times> 'l) \<Rightarrow> ('f \<times> 'l) \<Rightarrow> bool\<close> where
  "Labeled_Empty_Order C1 C2 \<equiv> False" 

sublocale labeled_lifted_calculus_with_red_crit: redundancy_criterion_lifting \<G>_F_L \<G>_Inf_L Bot_FL Inf_FL Bot_G entails_G Inf_G Red_Inf_G Red_F_G Labeled_Empty_Order
proof
  show "po_on Labeled_Empty_Order UNIV" unfolding Labeled_Empty_Order_def po_on_def by (simp add: transp_onI wfp_on_imp_irreflp_on)
  show "wfp_on Labeled_Empty_Order UNIV" unfolding wfp_on_def Labeled_Empty_Order_def by simp
qed

notation "labeled_standard_lifting.entails_\<G>" (infix "\<Turnstile>\<G>L" 50)

text \<open>Lemma 21 from the technical report\<close>
lemma labeled_entailment_lifting: "NL1 \<Turnstile>\<G>L NL2 \<longleftrightarrow> fst ` NL1 \<Turnstile>\<G> fst ` NL2"
  unfolding labeled_standard_lifting.entails_\<G>_def \<G>_F_L_def entails_\<G>_def by auto

lemma subset_fst: "A \<subseteq> fst ` AB \<Longrightarrow> \<forall>x \<in> A. \<exists>y. (x,y) \<in> AB" by fastforce

lemma red_inf_impl: "\<iota> \<in> labeled_lifted_calculus_with_red_crit.Red_Inf_\<G> NL \<Longrightarrow> to_F \<iota> \<in> Red_Inf_\<G> (fst ` NL)"
  unfolding labeled_lifted_calculus_with_red_crit.Red_Inf_\<G>_def Red_Inf_\<G>_def \<G>_Inf_L_def \<G>_F_L_def to_F_def
  using Inf_FL_to_Inf_F by auto

text \<open>lemma 22 from the technical report\<close>
lemma labeled_saturation_lifting: "labeled_lifted_calculus_with_red_crit.lifted_calculus_with_red_crit.saturated NL \<Longrightarrow> empty_order_lifting.lifted_calculus_with_red_crit.saturated (fst ` NL)"
  unfolding labeled_lifted_calculus_with_red_crit.lifted_calculus_with_red_crit.saturated_def empty_order_lifting.lifted_calculus_with_red_crit.saturated_def labeled_standard_lifting.Non_ground.Inf_from_def Non_ground.Inf_from_def
proof clarify
  fix \<iota>
  assume
    subs_Red_Inf: "{\<iota> \<in> Inf_FL. set (prems_of \<iota>) \<subseteq> NL} \<subseteq> labeled_lifted_calculus_with_red_crit.Red_Inf_\<G> NL" and
    i_in: "\<iota> \<in> Inf_F" and
    i_prems: "set (prems_of \<iota>) \<subseteq> fst ` NL"
  define Lli where "Lli i \<equiv> (SOME x. ((prems_of \<iota>)!i,x) \<in> NL)" for i
  have [simp]:"((prems_of \<iota>)!i,Lli i) \<in> NL" if "i < length (prems_of \<iota>)" for i
    using that subset_fst[OF i_prems] unfolding Lli_def by (meson nth_mem someI_ex)
  define Ll where "Ll \<equiv> map Lli [0..<length (prems_of \<iota>)]"
  have Ll_length: "length Ll = length (prems_of \<iota>)" unfolding Ll_def by auto
    (* "\<exists>L0. Infer (zip (prems_of \<iota>) Ll) (concl_of \<iota>, L0) \<in> Inf_FL" and *)
  have subs_NL: "set (zip (prems_of \<iota>) Ll) \<subseteq> NL" unfolding Ll_def by (auto simp:in_set_zip)
  obtain L0 where L0: "Infer (zip (prems_of \<iota>) Ll) (concl_of \<iota>, L0) \<in> Inf_FL"
    using Inf_F_to_Inf_FL[OF i_in Ll_length] ..
  define \<iota>_FL where "\<iota>_FL = Infer (zip (prems_of \<iota>) Ll) (concl_of \<iota>, L0)"
  then have "set (prems_of \<iota>_FL) \<subseteq> NL" using subs_NL by simp
  then have "\<iota>_FL \<in> {\<iota> \<in> Inf_FL. set (prems_of \<iota>) \<subseteq> NL}" unfolding \<iota>_FL_def using L0 by blast
  then have "\<iota>_FL \<in> labeled_lifted_calculus_with_red_crit.Red_Inf_\<G> NL" using subs_Red_Inf by fast
  moreover have "\<iota> = to_F \<iota>_FL" unfolding to_F_def \<iota>_FL_def using Ll_length by (cases \<iota>) auto
  ultimately show "\<iota> \<in> Red_Inf_\<G> (fst ` NL)" by (auto intro:red_inf_impl)
qed

text "lemma 23 from the technical report"
lemma "static_refutational_complete_calculus Bot_F Inf_F (\<Turnstile>\<G>) Red_Inf_\<G> Red_F_\<G> \<Longrightarrow> static_refutational_complete_calculus Bot_FL Inf_FL (\<Turnstile>\<G>L) labeled_lifted_calculus_with_red_crit.Red_Inf_\<G> labeled_lifted_calculus_with_red_crit.Red_F_\<G>"
  unfolding static_refutational_complete_calculus_def
proof (rule conjI impI; clarify)
  interpret calculus_with_red_crit Bot_FL Inf_FL labeled_standard_lifting.entails_\<G> labeled_lifted_calculus_with_red_crit.Red_Inf_\<G> labeled_lifted_calculus_with_red_crit.Red_F_\<G> by (simp add: labeled_lifted_calculus_with_red_crit.lifted_calculus_with_red_crit.calculus_with_red_crit_axioms)
  show "calculus_with_red_crit Bot_FL Inf_FL (\<Turnstile>\<G>L) labeled_lifted_calculus_with_red_crit.Red_Inf_\<G> labeled_lifted_calculus_with_red_crit.Red_F_\<G>" by standard
next
  assume
    calc: "calculus_with_red_crit Bot_F Inf_F (\<Turnstile>\<G>) Red_Inf_\<G> Red_F_\<G>" and
    static: "static_refutational_complete_calculus_axioms Bot_F Inf_F (\<Turnstile>\<G>) Red_Inf_\<G>"
  show "static_refutational_complete_calculus_axioms Bot_FL Inf_FL (\<Turnstile>\<G>L) labeled_lifted_calculus_with_red_crit.Red_Inf_\<G>" unfolding static_refutational_complete_calculus_axioms_def
  proof (intro conjI impI allI)
    fix Bl :: \<open>'f \<times> 'l\<close> and Nl :: \<open>('f \<times> 'l) set\<close>
    assume 
      Bl_in: \<open>Bl \<in> Bot_FL\<close> and
      Nl_sat: \<open>labeled_lifted_calculus_with_red_crit.empty_order_lifting.lifted_calculus_with_red_crit.saturated Nl\<close> and
      Nl_entails_Bl: \<open>Nl \<Turnstile>\<G>L {Bl}\<close>
    have static_axioms: "B \<in> Bot_F \<longrightarrow> empty_order_lifting.lifted_calculus_with_red_crit.saturated N \<longrightarrow> N \<Turnstile>\<G> {B} \<longrightarrow> (\<exists>B'\<in>Bot_F. B' \<in> N)" for B N using static[unfolded static_refutational_complete_calculus_axioms_def] by fast
    define B where "B = fst Bl"
    have B_in: "B \<in> Bot_F" using Bl_in Bot_FL_def B_def SigmaE by force
    define N where "N = fst ` Nl"
    have N_sat: "empty_order_lifting.lifted_calculus_with_red_crit.saturated N"
      using N_def Nl_sat labeled_saturation_lifting by blast 
    have N_entails_B: "N \<Turnstile>\<G> {B}" using Nl_entails_Bl unfolding labeled_entailment_lifting N_def B_def by force
    have "\<exists>B' \<in> Bot_F. B' \<in> N" using B_in N_sat N_entails_B static_axioms[of B N] by blast
    then obtain B' where in_Bot: "B' \<in> Bot_F" and in_N: "B' \<in> N" by force
    then have "B' \<in> fst ` Bot_FL" unfolding Bot_FL_def by fastforce
    obtain Bl' where in_Nl: "Bl' \<in> Nl" and fst_Bl': "fst Bl' = B'"
      using in_N unfolding N_def by blast
    have "Bl' \<in> Bot_FL" unfolding Bot_FL_def using fst_Bl' in_Bot vimage_fst by fastforce
    then show \<open>\<exists>Bl'\<in>Bot_FL. Bl' \<in> Nl\<close> using in_Nl by blast
  qed
qed

end

end
