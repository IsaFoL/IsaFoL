(*  Title:       Dynamic_Completeness_Lifting
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018
*)

theory Dynamic_Completeness_Lifting
  imports
    Saturation_Framework_Preliminaries
    Well_Quasi_Orders.Minimal_Elements
begin

subsection \<open>standard lifting\<close>

locale standard_lifting = Non_ground: inference_system Inf_F + Ground: calculus_with_red_crit Bot_G Inf_G entails_G Red_Inf_G Red_F_G
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

text \<open>lemma 25 in the technical report\<close>
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

lemma any_to_empty_order_lifting:
  "lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf Prec_F_g
  \<Longrightarrow> lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf (\<lambda>g. Empty_Order)"
proof -
  fix Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf Prec_F_g
  assume lift: "lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf Prec_F_g"
  then interpret lift_g:
    lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf Prec_F_g
    by auto
  have empty_wf: "minimal_element ((\<lambda>g. Empty_Order) g) UNIV"
    by (simp add: lift_g.all_wf Empty_Order_def minimal_element.intro po_on_def transp_on_def wfp_on_def
      wfp_on_imp_irreflp_on)
  then show "lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf (\<lambda>g. Empty_Order)"
    by (simp add: empty_wf lift_g.standard_lifting_axioms lifting_with_wf_ordering_family_axioms.intro lifting_with_wf_ordering_family_def)
qed


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


end
