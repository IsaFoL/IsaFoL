(*  Title:       Lifting to Non-Ground Calculi of the Saturation Framework
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018-2019
*)

theory Lifting_to_Non_Ground_Calculi
  imports
    Calculi
    Well_Quasi_Orders.Minimal_Elements
begin

locale standard_lifting = Non_ground: inference_system Inf_F +
  Ground: calculus_with_red_crit Bot_G Inf_G entails_G Red_Inf_G Red_F_G
  for
    Bot_F :: \<open>'f set\<close> and
    Inf_F :: \<open>'f inference set\<close> and
    Bot_G :: \<open>'g set\<close> and
    Inf_G ::  \<open>'g inference set\<close> and
    entails_G ::  \<open>'g set  \<Rightarrow> 'g set  \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    Red_Inf_G :: \<open>'g set \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g set \<Rightarrow> 'g set\<close>
  + fixes
    \<G>_F :: \<open>'f \<Rightarrow> 'g set\<close> and
    \<G>_Inf :: \<open>'f inference \<Rightarrow> 'g inference set\<close>
  assumes
    Bot_F_not_empty: "Bot_F \<noteq> {}" and
    Bot_map_not_empty: \<open>B \<in> Bot_F \<Longrightarrow> \<G>_F B \<noteq> {}\<close> and
    Bot_map: \<open>B \<in> Bot_F \<Longrightarrow> \<G>_F B \<subseteq> Bot_G\<close> and
    Bot_cond: \<open>\<G>_F C \<inter> Bot_G \<noteq> {} \<longrightarrow> C \<in> Bot_F\<close> and
    inf_map: \<open>\<iota> \<in> Inf_F \<Longrightarrow> \<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_F (concl_of \<iota>))\<close>
begin

abbreviation \<G>_set :: \<open>'f set \<Rightarrow> 'g set\<close> where
  \<open>\<G>_set N \<equiv> UNION N \<G>_F\<close> (*  \<Union>C \<in> N. \<G>_F C *)

lemma \<G>_subset: \<open>N1 \<subseteq> N2 \<Longrightarrow> \<G>_set N1 \<subseteq> \<G>_set N2\<close> by auto

definition entails_\<G>  :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix "\<Turnstile>\<G>" 50) where
  \<open>N1 \<Turnstile>\<G> N2 \<equiv> \<G>_set N1 \<Turnstile>G \<G>_set N2\<close>

lemma subs_Bot_G_entails: 
  assumes
    not_empty: \<open>sB \<noteq> {}\<close> and
    in_bot: \<open>sB \<subseteq> Bot_G\<close>
  shows \<open>sB \<Turnstile>G N\<close>
proof -
  have \<open>\<exists>B. B \<in> sB\<close> using not_empty by auto
  then obtain B where B_in: \<open>B \<in> sB\<close> by auto
  then have r_trans: \<open>{B} \<Turnstile>G N\<close> using Ground.bot_implies_all in_bot by auto
  have l_trans: \<open>sB \<Turnstile>G {B}\<close> using B_in Ground.subset_entailed by auto
  then show ?thesis using r_trans Ground.entails_trans[of sB "{B}"] by auto
qed

text \<open>lemma:derived-consequence-relation\<close>
sublocale lifted_consequence_relation: consequence_relation  
  where Bot=Bot_F and entails=entails_\<G>
proof
  show "Bot_F \<noteq> {}" using Bot_F_not_empty .
next
  show \<open>B\<in>Bot_F \<Longrightarrow> {B} \<Turnstile>\<G> N\<close> for B N 
  proof -
    assume \<open>B \<in> Bot_F\<close>
    then show \<open>{B} \<Turnstile>\<G> N\<close>
      using Bot_map Ground.bot_implies_all[of _ "\<G>_set N"] subs_Bot_G_entails Bot_map_not_empty
      unfolding entails_\<G>_def
      by auto
  qed
next
  fix N1 N2 :: \<open>'f set\<close>
  assume 
    \<open>N2 \<subseteq> N1\<close>
  then show \<open>N1 \<Turnstile>\<G> N2\<close> using entails_\<G>_def \<G>_subset Ground.subset_entailed by auto
next
  fix N1 N2
  assume
    N1_entails_C: \<open>\<forall>C \<in> N2. N1 \<Turnstile>\<G> {C}\<close>
  show \<open>N1 \<Turnstile>\<G> N2\<close> using Ground.all_formulas_entailed N1_entails_C entails_\<G>_def 
    by (smt UN_E UN_I Ground.entail_set_all_formulas singletonI)
next
  fix N1 N2 N3
  assume
    \<open>N1 \<Turnstile>\<G> N2\<close> and \<open>N2 \<Turnstile>\<G> N3\<close>
  then show \<open>N1 \<Turnstile>\<G> N3\<close> using entails_\<G>_def Ground.entails_trans by blast
qed

end

locale lifting_with_wf_ordering_family =
  standard_lifting Bot_F Inf_F Bot_G Inf_G entails_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf
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

text \<open>lemma:wolog-C'-nonredundant\<close>
lemma Red_F_\<G>_equiv_def: 
  \<open>Red_F_\<G> N = {C. \<forall>Di \<in> \<G>_F C. Di \<in> Red_F_G (\<G>_set N) \<or>
    (\<exists>E \<in> (N - Red_F_\<G> N). Prec_F_g Di E C \<and> Di \<in> \<G>_F E)}\<close>
proof (rule;clarsimp)
  fix C D
  assume 
    C_in: \<open>C \<in> Red_F_\<G> N\<close> and
    D_in: \<open>D \<in> \<G>_F C\<close> and
    not_sec_case: \<open>\<forall>E \<in> N - Red_F_\<G> N. Prec_F_g D E C \<longrightarrow> D \<notin> \<G>_F E\<close>
  have C_in_unfolded: "C \<in> {C. \<forall>Di \<in> \<G>_F C. Di \<in> Red_F_G (\<G>_set N) \<or>
    (\<exists>E\<in>N. Prec_F_g Di E C \<and> Di \<in> \<G>_F E)}"
    using C_in unfolding Red_F_\<G>_def .
  have neg_not_sec_case: \<open>\<not> (\<exists>E\<in>N - Red_F_\<G> N. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
    using not_sec_case by clarsimp 
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
      by (smt Sup_UNIV Sup_upper UNIV_I contra_subsetD empty_iff empty_subsetI mem_Collect_eq
        min_elt_mem unfol_C_D) 
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

text \<open>lemma:lifting-main-technical\<close>
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

text \<open>lemma:nonredundant-entails-redundant\<close>
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

text \<open>lemma:redundancy-monotonic-addition 1/2\<close>
lemma Red_F_of_subset_F: \<open>N \<subseteq> N' \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> N'\<close>
  using Ground.Red_F_of_subset unfolding Red_F_\<G>_def by (smt Collect_mono \<G>_subset subset_iff)

text \<open>lemma:redundancy-monotonic-addition 2/2\<close>
lemma Red_Inf_of_subset_F: \<open>N \<subseteq> N' \<Longrightarrow> Red_Inf_\<G> N \<subseteq> Red_Inf_\<G> N'\<close>
  using Ground.Red_Inf_of_subset unfolding Red_Inf_\<G>_def by (smt Collect_mono \<G>_subset subset_iff)

text \<open>lemma:redundancy-monotonic-deletion-forms\<close>
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

text \<open>lemma:redundancy-monotonic-deletion-infs\<close>
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

text \<open>lemma:concl-contained-implies-red-inf\<close>
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

text \<open>thm:FRedsqsubset-is-red-crit\<close>
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

lemma "calculus_with_red_crit Bot_F Inf_F entails_\<G> Red_Inf_\<G> Red_F_\<G>"
  using lifted_calculus_with_red_crit.calculus_with_red_crit_axioms .

end

definition Empty_Order :: \<open>'f \<Rightarrow> 'f \<Rightarrow> bool\<close> where
  "Empty_Order C1 C2 \<equiv> False" 

lemma any_to_empty_order_lifting:
  "lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F
    \<G>_Inf Prec_F_g \<Longrightarrow> lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G
    Red_F_G \<G>_F \<G>_Inf (\<lambda>g. Empty_Order)"
proof -
  fix Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf Prec_F_g
  assume lift: "lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G
    Red_F_G \<G>_F \<G>_Inf Prec_F_g"
  then interpret lift_g:
    lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F
      \<G>_Inf Prec_F_g
    by auto
  have empty_wf: "minimal_element ((\<lambda>g. Empty_Order) g) UNIV"
    by (simp add: lift_g.all_wf Empty_Order_def minimal_element.intro po_on_def transp_on_def wfp_on_def
      wfp_on_imp_irreflp_on)
  then show "lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G
    \<G>_F \<G>_Inf (\<lambda>g. Empty_Order)"
    by (simp add: empty_wf lift_g.standard_lifting_axioms
      lifting_with_wf_ordering_family_axioms.intro lifting_with_wf_ordering_family_def)
qed

(* TODO: there may be a way to merge this locale with the previous one *)
locale lifting_equivalence_with_empty_order =
  any_order_lifting: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G
    Red_F_G \<G>_F \<G>_Inf Prec_F_g +
  empty_order_lifting: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G
    Red_F_G \<G>_F \<G>_Inf "\<lambda>g. Empty_Order"
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
  show "po_on Empty_Order UNIV"
    unfolding Empty_Order_def po_on_def by (simp add: transp_onI wfp_on_imp_irreflp_on)
  show "wfp_on Empty_Order UNIV"
    unfolding wfp_on_def Empty_Order_def by simp
qed

context lifting_equivalence_with_empty_order
begin

text "lemma:saturation-indep-of-sqsubset"
lemma saturated_empty_order_equiv_saturated:
  "any_order_lifting.lifted_calculus_with_red_crit.saturated N =
    empty_order_lifting.lifted_calculus_with_red_crit.saturated N" by standard

text "lemma:static-ref-compl-indep-of-sqsubset"
lemma static_empty_order_equiv_static:
  "static_refutational_complete_calculus Bot_F Inf_F
    any_order_lifting.entails_\<G> empty_order_lifting.Red_Inf_\<G> empty_order_lifting.Red_F_\<G> =
    static_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G> any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>"
  unfolding static_refutational_complete_calculus_def
  by (rule iffI) (standard,(standard)[],simp)+
   
text "thm:FRedsqsubset-is-dyn-ref-compl"
theorem static_to_dynamic:
  "static_refutational_complete_calculus Bot_F Inf_F
    any_order_lifting.entails_\<G> empty_order_lifting.Red_Inf_\<G> empty_order_lifting.Red_F_\<G> =
    dynamic_refutational_complete_calculus Bot_F Inf_F
    any_order_lifting.entails_\<G> any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G> "
  (is "?static=?dynamic")
proof
  assume ?static
  then have static_general:
    "static_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G>
      any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>" (is "?static_gen")
    using static_empty_order_equiv_static by simp
  interpret static_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G>
    any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>
    using static_general .
  show "?dynamic" by standard 
next
  assume dynamic_gen: ?dynamic
  interpret dynamic_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G>
    any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>
    using dynamic_gen .
  have "static_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G>
    any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>"
    by standard
  then show "?static" using static_empty_order_equiv_static by simp
qed

end

locale standard_lifting_with_red_crit_family = Non_ground: inference_system Inf_F
  + Ground_family: calculus_with_red_crit_family Bot_G Inf_G Q entails_q Red_Inf_q Red_F_q
  for
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    Inf_G :: \<open>'g inference set\<close> and
    Q :: "'q itself" and
    entails_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g set \<Rightarrow> bool)" and
    Red_Inf_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g inference set)" and
    Red_F_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g set)"
  + fixes
    Bot_F :: "'f set" and
    \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set" and
    \<G>_Inf_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set" and
    Prec_F_g :: "'g \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool"
  assumes
    standard_lifting_family: "lifting_with_wf_ordering_family Bot_F Inf_F Bot_G (entails_q q)
      Inf_G (Red_Inf_q q) (Red_F_q q) (\<G>_F_q q) (\<G>_Inf_q q) Prec_F_g" 
begin

definition \<G>_set_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'g set" where
  "\<G>_set_q q N \<equiv> UNION N (\<G>_F_q q)"

definition Red_Inf_\<G>_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f inference set" where
  "Red_Inf_\<G>_q q N = {\<iota> \<in> Inf_F. \<G>_Inf_q q \<iota> \<subseteq> Red_Inf_q q (\<G>_set_q q N)}"

definition Red_Inf_\<G>_Q :: "'f set \<Rightarrow> 'f inference set" where
  "Red_Inf_\<G>_Q N = \<Inter> {X N |X. X \<in> (Red_Inf_\<G>_q ` UNIV)}"

definition Red_F_\<G>_empty_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_empty_q q N = {C. \<forall>D \<in> \<G>_F_q q C. D \<in> Red_F_q q (\<G>_set_q q N) \<or> (\<exists>E \<in> N. Empty_Order E C \<and> D \<in> \<G>_F_q q E)}"

definition Red_F_\<G>_empty :: "'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_empty N = \<Inter> {X N |X. X \<in> (Red_F_\<G>_empty_q ` UNIV)}"

definition Red_F_\<G>_q_g :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_q_g q N = {C. \<forall>D \<in> \<G>_F_q q C. D \<in> Red_F_q q (\<G>_set_q q N) \<or> (\<exists>E \<in> N. Prec_F_g D E C \<and> D \<in> \<G>_F_q q E)}"

definition Red_F_\<G>_g :: "'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_g N = \<Inter> {X N |X. X \<in> (Red_F_\<G>_q_g ` UNIV)}"

definition entails_\<G>_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> bool" where
  "entails_\<G>_q q N1 N2 \<equiv> entails_q q (\<G>_set_q q N1) (\<G>_set_q q N2)"

definition entails_\<G>_Q :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" where
  "entails_\<G>_Q N1 N2 \<equiv> \<forall>q. entails_\<G>_q q N1 N2"

lemma red_crit_lifting_family:
  "calculus_with_red_crit Bot_F Inf_F (entails_\<G>_q q) (Red_Inf_\<G>_q q) (Red_F_\<G>_q_g q)"
proof -
  fix q
  interpret wf_lift:
    lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q q" Inf_G "Red_Inf_q q" "Red_F_q q"
      "\<G>_F_q q" "\<G>_Inf_q q" Prec_F_g
    using standard_lifting_family .
  have "entails_\<G>_q q = wf_lift.entails_\<G>"
    unfolding entails_\<G>_q_def wf_lift.entails_\<G>_def \<G>_set_q_def by blast
  moreover have "Red_Inf_\<G>_q q = wf_lift.Red_Inf_\<G>"
    unfolding Red_Inf_\<G>_q_def \<G>_set_q_def wf_lift.Red_Inf_\<G>_def by blast
  moreover have "Red_F_\<G>_q_g q = wf_lift.Red_F_\<G>"
    unfolding Red_F_\<G>_q_g_def \<G>_set_q_def wf_lift.Red_F_\<G>_def by blast
  ultimately show "calculus_with_red_crit Bot_F Inf_F (entails_\<G>_q q) (Red_Inf_\<G>_q q) (Red_F_\<G>_q_g q)"
    using wf_lift.lifted_calculus_with_red_crit.calculus_with_red_crit_axioms by simp
qed


lemma red_crit_lifting_family_empty_ord:
  "calculus_with_red_crit Bot_F Inf_F (entails_\<G>_q q) (Red_Inf_\<G>_q q) (Red_F_\<G>_empty_q q)"
proof -
  fix q
  interpret wf_lift:
    lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q q" Inf_G "Red_Inf_q q" "Red_F_q q"
      "\<G>_F_q q" "\<G>_Inf_q q" Prec_F_g
    using standard_lifting_family .
  have "entails_\<G>_q q = wf_lift.entails_\<G>"
    unfolding entails_\<G>_q_def wf_lift.entails_\<G>_def \<G>_set_q_def by blast
  moreover have "Red_Inf_\<G>_q q = wf_lift.Red_Inf_\<G>"
    unfolding Red_Inf_\<G>_q_def \<G>_set_q_def wf_lift.Red_Inf_\<G>_def by blast
  moreover have "Red_F_\<G>_empty_q q = wf_lift.empty_order_lifting.Red_F_\<G>"
    unfolding Red_F_\<G>_empty_q_def \<G>_set_q_def wf_lift.empty_order_lifting.Red_F_\<G>_def by blast
  ultimately show "calculus_with_red_crit Bot_F Inf_F (entails_\<G>_q q) (Red_Inf_\<G>_q q) (Red_F_\<G>_empty_q q)"
    using wf_lift.empty_order_lifting.lifted_calculus_with_red_crit.calculus_with_red_crit_axioms
    by simp
qed

lemma cons_rel_fam_Q_lem: \<open>consequence_relation_family Bot_F entails_\<G>_q\<close>
proof
  show "Bot_F \<noteq> {}"
    using standard_lifting_family 
    by (meson ex_in_conv lifting_with_wf_ordering_family.axioms(1) standard_lifting.Bot_F_not_empty)
next
  fix qi
  show "Bot_F \<noteq> {}"
    using standard_lifting_family
    by (meson ex_in_conv lifting_with_wf_ordering_family.axioms(1) standard_lifting.Bot_F_not_empty)
next
  fix qi B N1
  assume
    B_in: "B \<in> Bot_F"
  interpret lift: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q qi" Inf_G "Red_Inf_q qi"
    "Red_F_q qi" "\<G>_F_q qi" "\<G>_Inf_q qi" Prec_F_g
    by (rule standard_lifting_family)
  have "(entails_\<G>_q qi) = lift.entails_\<G>"
    unfolding entails_\<G>_q_def lift.entails_\<G>_def \<G>_set_q_def by simp
  then show "entails_\<G>_q qi {B} N1"
    using B_in lift.lifted_consequence_relation.bot_implies_all by auto
next
  fix qi and N2 N1::"'f set"
  assume
    N_incl: "N2 \<subseteq> N1"
  interpret lift: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q qi" Inf_G "Red_Inf_q qi"
   "Red_F_q qi" "\<G>_F_q qi" "\<G>_Inf_q qi" Prec_F_g
    by (rule standard_lifting_family)
  have "(entails_\<G>_q qi) = lift.entails_\<G>"
    unfolding entails_\<G>_q_def lift.entails_\<G>_def \<G>_set_q_def by simp
  then show "entails_\<G>_q qi N1 N2"
    using N_incl by (simp add: lift.lifted_consequence_relation.subset_entailed)
next
  fix qi N1 N2
  assume
    all_C: "\<forall>C\<in> N2. entails_\<G>_q qi N1 {C}"
  interpret lift: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q qi" Inf_G "Red_Inf_q qi"
    "Red_F_q qi" "\<G>_F_q qi" "\<G>_Inf_q qi" Prec_F_g
    by (rule standard_lifting_family)
  have "(entails_\<G>_q qi) = lift.entails_\<G>"
    unfolding entails_\<G>_q_def lift.entails_\<G>_def \<G>_set_q_def by simp
  then show "entails_\<G>_q qi N1 N2"
    using all_C lift.lifted_consequence_relation.all_formulas_entailed by presburger
next
  fix qi N1 N2 N3
  assume
    entails12: "entails_\<G>_q qi N1 N2" and
    entails23: "entails_\<G>_q qi N2 N3"
  interpret lift: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q qi" Inf_G "Red_Inf_q qi"
    "Red_F_q qi" "\<G>_F_q qi" "\<G>_Inf_q qi" Prec_F_g
    by (rule standard_lifting_family)
  have "(entails_\<G>_q qi) = lift.entails_\<G>"
    unfolding entails_\<G>_q_def lift.entails_\<G>_def \<G>_set_q_def by simp
  then show "entails_\<G>_q qi N1 N3"
    using entails12 entails23 lift.lifted_consequence_relation.entails_trans by presburger
qed

interpretation cons_rel_Q: consequence_relation Bot_F entails_\<G>_Q
proof -
  interpret cons_rel_fam: consequence_relation_family Bot_F Q entails_\<G>_q
    by (rule cons_rel_fam_Q_lem)
  have "consequence_relation_family.entails_Q entails_\<G>_q = entails_\<G>_Q"
    unfolding entails_\<G>_Q_def cons_rel_fam.entails_Q_def by (simp add: entails_\<G>_q_def)
  then show "consequence_relation Bot_F entails_\<G>_Q"
    using consequence_relation_family.cons_rel_family_is_cons_rel[OF cons_rel_fam_Q_lem] by simp
qed

sublocale lifted_calc_w_red_crit_family:
  calculus_with_red_crit_family Bot_F Inf_F Q entails_\<G>_q Red_Inf_\<G>_q Red_F_\<G>_q_g
  using cons_rel_fam_Q_lem red_crit_lifting_family
  by (simp add: calculus_with_red_crit_family.intro calculus_with_red_crit_family_axioms_def)

lemma "calculus_with_red_crit Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_g"
proof -
  have "lifted_calc_w_red_crit_family.entails_Q = entails_\<G>_Q"
    unfolding entails_\<G>_Q_def lifted_calc_w_red_crit_family.entails_Q_def by simp
  moreover have "lifted_calc_w_red_crit_family.Red_Inf_Q = Red_Inf_\<G>_Q"
    unfolding Red_Inf_\<G>_Q_def lifted_calc_w_red_crit_family.Red_Inf_Q_def by simp 
  moreover have "lifted_calc_w_red_crit_family.Red_F_Q = Red_F_\<G>_g"
    unfolding Red_F_\<G>_g_def lifted_calc_w_red_crit_family.Red_F_Q_def by simp
  ultimately show "calculus_with_red_crit Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_g"
  using lifted_calc_w_red_crit_family.inter_red_crit by simp
qed

sublocale empty_ord_lifted_calc_w_red_crit_family:
  calculus_with_red_crit_family Bot_F Inf_F Q entails_\<G>_q Red_Inf_\<G>_q Red_F_\<G>_empty_q
  using cons_rel_fam_Q_lem red_crit_lifting_family_empty_ord
  by (simp add: calculus_with_red_crit_family.intro calculus_with_red_crit_family_axioms_def)

lemma "calculus_with_red_crit Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_empty"
proof -
  have "lifted_calc_w_red_crit_family.entails_Q = entails_\<G>_Q"
    unfolding entails_\<G>_Q_def lifted_calc_w_red_crit_family.entails_Q_def by simp
  moreover have "empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q = Red_Inf_\<G>_Q"
    unfolding Red_Inf_\<G>_Q_def lifted_calc_w_red_crit_family.Red_Inf_Q_def by simp 
  moreover have "empty_ord_lifted_calc_w_red_crit_family.Red_F_Q = Red_F_\<G>_empty"
    unfolding Red_F_\<G>_empty_def empty_ord_lifted_calc_w_red_crit_family.Red_F_Q_def by simp
  ultimately show "calculus_with_red_crit Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_empty"
  using empty_ord_lifted_calc_w_red_crit_family.inter_red_crit by simp
qed

text "lemma:intersect-saturation-indep-of-sqsubset"
lemma "lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated N =
  empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated N "
  by simp

text "lemma:intersect-static-ref-compl-indep-of-sqsubset"
lemma static_empty_ord_inter_equiv_static_inter:
  "static_refutational_complete_calculus Bot_F Inf_F lifted_calc_w_red_crit_family.entails_Q
    lifted_calc_w_red_crit_family.Red_Inf_Q lifted_calc_w_red_crit_family.Red_F_Q =
  static_refutational_complete_calculus Bot_F Inf_F lifted_calc_w_red_crit_family.entails_Q
    empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q empty_ord_lifted_calc_w_red_crit_family.Red_F_Q"
  unfolding static_refutational_complete_calculus_def
  by (simp add: empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.calculus_with_red_crit_axioms
    lifted_calc_w_red_crit_family.inter_red_crit_calculus.calculus_with_red_crit_axioms)

text "thm:intersect-static-ref-compl-is-dyn-ref-compl-with-order"
theorem "static_refutational_complete_calculus Bot_F Inf_F lifted_calc_w_red_crit_family.entails_Q
    empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q empty_ord_lifted_calc_w_red_crit_family.Red_F_Q =
  dynamic_refutational_complete_calculus Bot_F Inf_F lifted_calc_w_red_crit_family.entails_Q
    lifted_calc_w_red_crit_family.Red_Inf_Q lifted_calc_w_red_crit_family.Red_F_Q"  (is "?static=?dynamic")
proof
  assume ?static
  then have static_general: "static_refutational_complete_calculus Bot_F Inf_F
    lifted_calc_w_red_crit_family.entails_Q lifted_calc_w_red_crit_family.Red_Inf_Q
    lifted_calc_w_red_crit_family.Red_F_Q" (is "?static_gen")
    using static_empty_ord_inter_equiv_static_inter
    by simp
  interpret static_refutational_complete_calculus Bot_F Inf_F lifted_calc_w_red_crit_family.entails_Q
    lifted_calc_w_red_crit_family.Red_Inf_Q lifted_calc_w_red_crit_family.Red_F_Q
    using static_general .
  show "?dynamic" by standard 
next
  assume dynamic_gen: ?dynamic
  interpret dynamic_refutational_complete_calculus Bot_F Inf_F lifted_calc_w_red_crit_family.entails_Q
    lifted_calc_w_red_crit_family.Red_Inf_Q lifted_calc_w_red_crit_family.Red_F_Q
    using dynamic_gen .
  have "static_refutational_complete_calculus Bot_F Inf_F lifted_calc_w_red_crit_family.entails_Q
    lifted_calc_w_red_crit_family.Red_Inf_Q lifted_calc_w_red_crit_family.Red_F_Q"
    by standard
  then show "?static" using static_empty_ord_inter_equiv_static_inter by simp
qed

end

end