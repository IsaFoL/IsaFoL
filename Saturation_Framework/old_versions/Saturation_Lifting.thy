theory Saturation_Lifting
  imports
    Saturation_Framework
    Well_Quasi_Orders.Minimal_Elements
begin

locale redundancy_criterion_lifting = calculus Bot_G entails_G Inf_G Red_Inf_G Red_F_G
  + minimal_element Prec_F UNIV
  for
    Bot_G :: \<open>'g set\<close> and
    entails_G :: \<open>'g set \<Rightarrow> 'g set \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    Inf_G :: \<open>'g inference set\<close> and
    Red_Inf_G :: \<open>'g set \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g set \<Rightarrow> 'g set\<close> and
    Prec_F :: \<open>'f \<Rightarrow> 'f \<Rightarrow> bool\<close> (infix "\<sqsubset>" 50)
  + fixes
    Bot_F :: \<open>'f set\<close> and
    Inf_F :: \<open>'f inference set\<close> and
    \<G>_F :: \<open>'f \<Rightarrow> 'g set\<close> and
    \<G>_Inf :: \<open>'f inference \<Rightarrow> 'g inference set\<close>
  assumes
    Bot_map_not_empty: \<open>\<forall>B \<in> Bot_F. \<G>_F B \<noteq> {}\<close> and
    Bot_map: \<open>\<forall>B \<in> Bot_F. \<G>_F B \<subseteq> Bot_G\<close> and
    inf_map: \<open>\<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_F (concl_of \<iota>))\<close>
begin

abbreviation \<G>_set :: \<open>'f set \<Rightarrow> 'g set\<close> where
  \<open>\<G>_set N \<equiv> \<Union>C \<in> N. \<G>_F C\<close>

lemma \<G>_subset: \<open>N1 \<subseteq> N2 \<Longrightarrow> \<G>_set N1 \<subseteq> \<G>_set N2\<close> by auto

definition entails_\<G>  :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix "\<Turnstile>\<G>" 50) where
\<open>N1 \<Turnstile>\<G> N2 \<equiv> (\<G>_set N1) \<Turnstile>G (\<G>_set N2)\<close>

lemma subs_Bot_G_entails: 
  assumes
    not_empty: \<open>sB \<noteq> {}\<close> and
    in_bot: \<open>sB \<subseteq> Bot_G\<close>
  shows \<open>sB \<Turnstile>G N\<close>
proof -
  have \<open>\<exists>B. B \<in> sB\<close> using not_empty by auto
  then obtain B where B_in: \<open>B \<in> sB\<close> by auto
  then have r_trans: \<open>{B} \<Turnstile>G N\<close> using bot_implies_all in_bot by auto
  have l_trans: \<open>sB \<Turnstile>G {B}\<close> using B_in subset_entailed by auto
  then show ?thesis using r_trans entails_trans[of sB "{B}"] by auto
qed

text \<open>lemma 7 in Uwe's notes\<close>
interpretation lifted_consequence_relation: consequence_relation  
  where Bot=Bot_F and entails=entails_\<G>
proof
  fix N
  show \<open>\<forall>B\<in>Bot_F. {B} \<Turnstile>\<G> N\<close> 
  proof
    fix B
    assume \<open>B\<in> Bot_F\<close>
    then show \<open>{B} \<Turnstile>\<G> N\<close> 
      using Bot_map bot_implies_all[of "\<G>_set N"] subs_Bot_G_entails Bot_map_not_empty
      unfolding entails_\<G>_def
      by auto
  qed
next
  fix N1 N2 :: \<open>'f set\<close>
  assume 
    incl: \<open>N2 \<subseteq> N1\<close>
  show \<open>N1 \<Turnstile>\<G> N2\<close> using incl entails_\<G>_def \<G>_subset subset_entailed by auto
next
  fix N1 N2
  assume
    N1_entails_C: \<open>\<forall>C \<in> N2. N1 \<Turnstile>\<G> {C}\<close>
  show \<open>N1 \<Turnstile>\<G> N2\<close> using all_formulas_entailed N1_entails_C entails_\<G>_def 
    by (smt UN_E UN_I entail_set_all_formulas singletonI)
next
  fix N1 N2 N3
  assume
    trans: \<open>N1 \<Turnstile>\<G> N2 \<and> N2 \<Turnstile>\<G> N3\<close>
  show \<open>N1 \<Turnstile>\<G> N3\<close> using trans entails_\<G>_def entails_trans by blast
qed

definition Red_Inf_\<G> :: "'f set \<Rightarrow> 'f inference set" where
  \<open>Red_Inf_\<G> N = {\<iota> \<in> Inf_F. \<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_set N)}\<close>

definition Red_F_\<G> :: "'f set \<Rightarrow> 'f set" where
  \<open>Red_F_\<G> N = {C. \<forall>D \<in> \<G>_F C. D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E \<in> N. E \<sqsubset> C \<and> D \<in> \<G>_F E)}\<close>

lemma Prec_trans: 
  assumes 
    \<open>A \<sqsubset> B\<close> and
    \<open>B \<sqsubset> C\<close>
  shows
    \<open>A \<sqsubset> C\<close>
  using po assms unfolding po_on_def transp_on_def by blast

text \<open>lemma 8 in Uwe's notes\<close>
lemma Red_F_\<G>_equiv_def: 
  \<open>Red_F_\<G> N = {C. \<forall>D \<in> \<G>_F C. D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E \<in> (N - Red_F_\<G> N). E \<sqsubset> C \<and> D \<in> \<G>_F E)}\<close>
proof (rule;clarsimp)
  fix C D
  assume 
    C_in: \<open>C \<in> Red_F_\<G> N\<close> and
    D_in: \<open>D \<in> \<G>_F C\<close> and
    not_sec_case: \<open>\<forall>E \<in> N - Red_F_\<G> N. E \<sqsubset> C \<longrightarrow> D \<notin> \<G>_F E\<close>
  have neg_not_sec_case: \<open>\<not> (\<exists>E\<in>N - Red_F_\<G> N. E \<sqsubset> C \<and> D \<in> \<G>_F E)\<close> using not_sec_case by clarsimp 
  have unfol_C_D: \<open>D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E\<in>N. E \<sqsubset> C \<and> D \<in> \<G>_F E)\<close> 
    using C_in D_in unfolding Red_F_\<G>_def by auto
  show \<open>D \<in> Red_F_G (\<G>_set N)\<close> 
  proof (rule ccontr)
    assume contrad: \<open>D \<notin> Red_F_G (\<G>_set N)\<close>
    have non_empty: \<open>\<exists>E\<in>N. E \<sqsubset> C \<and> D \<in> \<G>_F E\<close> using contrad unfol_C_D by auto
    define B where \<open>B = {E \<in> N. E \<sqsubset> C \<and> D \<in> \<G>_F E}\<close>
    then have B_non_empty: \<open>B \<noteq> {}\<close> using non_empty by auto
    obtain F where F: \<open>F = min_elt B\<close> by auto
    then have D_in_F: \<open>D \<in> \<G>_F F\<close> unfolding B_def using non_empty
      by (smt Sup_UNIV Sup_upper UNIV_I contra_subsetD empty_iff empty_subsetI mem_Collect_eq 
          min_elt_mem unfol_C_D)
    have F_prec: \<open>F \<sqsubset> C\<close> using F min_elt_mem[of B, OF _ B_non_empty] unfolding B_def by auto
    have F_not_in: \<open>F \<notin> Red_F_\<G> N\<close>
    proof
      assume F_in: \<open>F \<in> Red_F_\<G> N\<close>
      have unfol_F_D: \<open>D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>G\<in>N. G \<sqsubset> F \<and> D \<in> \<G>_F G)\<close>
        using F_in D_in_F unfolding Red_F_\<G>_def by auto
      then have \<open>\<exists>G\<in>N. G \<sqsubset> F \<and> D \<in> \<G>_F G\<close> using contrad D_in unfolding Red_F_\<G>_def by auto
      then obtain G where G_in: \<open>G \<in> N\<close> and G_prec: \<open>G \<sqsubset> F\<close> and G_map: \<open>D \<in> \<G>_F G\<close> by auto
      have \<open>G \<sqsubset> C\<close> using G_prec F_prec Prec_trans by blast
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
  assume only_if: \<open>\<forall>D\<in>\<G>_F C. D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E\<in>N - Red_F_\<G> N. E \<sqsubset> C \<and> D \<in> \<G>_F E)\<close>
  show \<open>C \<in> Red_F_\<G> N\<close> unfolding Red_F_\<G>_def using only_if by auto
qed

text \<open>lemma 9 in Uwe's notes\<close>
lemma not_red_map_in_map_not_red: \<open>\<G>_set N - Red_F_G (\<G>_set N) \<subseteq> \<G>_set (N - Red_F_\<G> N)\<close>
proof
  fix D
  assume
    D_hyp: \<open>D \<in> \<G>_set N - Red_F_G (\<G>_set N)\<close>
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
    have \<open>D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E\<in>N. E \<sqsubset> C \<and> D \<in> \<G>_F E)\<close>
      using C_in D_in_C unfolding Red_F_\<G>_def by auto
    then show \<open>False\<close>
      proof
        assume \<open>D \<in> Red_F_G (\<G>_set N)\<close>
        then show \<open>False\<close> using D_not_in by simp
      next
        assume \<open>\<exists>E\<in>N. E \<sqsubset> C \<and> D \<in> \<G>_F E\<close>
        then show \<open>False\<close> 
          using C by (metis (no_types, lifting) B_def UNIV_I empty_iff mem_Collect_eq 
              min_elt_minimal top_greatest)
      qed
  qed
  show \<open>D \<in> \<G>_set (N - Red_F_\<G> N)\<close> using D_in_C C_not_in C_in_N by blast
qed

text \<open>lemma 10 in Uwe's notes\<close>
lemma Red_F_Bot_F: \<open>B \<in> Bot_F \<Longrightarrow> N \<Turnstile>\<G> {B} \<Longrightarrow> N - Red_F_\<G> N \<Turnstile>\<G> {B}\<close>
proof -
  fix B N
  assume
    B_in: \<open>B \<in> Bot_F\<close> and
    N_entails: \<open>N \<Turnstile>\<G> {B}\<close>
  then have to_bot: \<open>\<G>_set N - Red_F_G (\<G>_set N) \<Turnstile>G \<G>_F B\<close> 
    using Red_F_Bot Bot_map unfolding entails_\<G>_def 
      by (smt cSup_singleton entail_set_all_formulas image_insert image_is_empty subsetCE)
  have from_f: \<open>\<G>_set (N - Red_F_\<G> N) \<Turnstile>G \<G>_set N - Red_F_G (\<G>_set N)\<close>
    using subset_entailed[OF not_red_map_in_map_not_red] by blast
  then have \<open>\<G>_set (N - Red_F_\<G> N) \<Turnstile>G \<G>_F B\<close> using to_bot entails_trans by blast
  then show \<open>N - Red_F_\<G> N \<Turnstile>\<G> {B}\<close> using Bot_map unfolding entails_\<G>_def by simp
qed

text \<open>lemma 11 in Uwe's notes 1/2\<close>
lemma Red_F_of_subset_F: \<open>N \<subseteq> N' \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> N'\<close>
  using Red_F_of_subset unfolding Red_F_\<G>_def by (smt Collect_mono \<G>_subset subset_iff)

text \<open>lemma 11 in Uwe's notes 2/2\<close>
lemma Red_Inf_of_subset_F: \<open>N \<subseteq> N' \<Longrightarrow> Red_Inf_\<G> N \<subseteq> Red_Inf_\<G> N'\<close>
  using Red_Inf_of_subset unfolding Red_Inf_\<G>_def by (smt Collect_mono \<G>_subset subset_iff)

text \<open>lemma 12 in Uwe's notes\<close>
lemma Red_F_of_Red_F_subset_F: \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> (N - N')\<close>
proof
  fix N N' C
  assume 
    N'_in_Red_F_N: \<open>N' \<subseteq> Red_F_\<G> N\<close> and
    C_in_red_F_N: \<open>C \<in> Red_F_\<G> N\<close>
  have lem8: \<open>\<forall>D \<in> \<G>_F C. D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E \<in> (N - Red_F_\<G> N). E \<sqsubset> C \<and> D \<in> \<G>_F E)\<close>
    using Red_F_\<G>_equiv_def C_in_red_F_N by blast
  show \<open>C \<in> Red_F_\<G> (N - N')\<close> unfolding Red_F_\<G>_def
  proof (rule,rule)
    fix D
    assume \<open>D \<in> \<G>_F C\<close>
    then have \<open>D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E \<in> (N - Red_F_\<G> N). E \<sqsubset> C \<and> D \<in> \<G>_F E)\<close>
      using lem8 by auto
    then show \<open>D \<in> Red_F_G (\<G>_set (N - N')) \<or> (\<exists>E\<in>N - N'. E \<sqsubset> C \<and> D \<in> \<G>_F E)\<close>
    proof
      assume \<open>D \<in> Red_F_G (\<G>_set N)\<close>
      then have \<open>D \<in> Red_F_G (\<G>_set N - Red_F_G (\<G>_set N))\<close>
        using Red_F_of_Red_F_subset[of "Red_F_G (\<G>_set N)" "\<G>_set N"] by auto
      then have \<open>D \<in> Red_F_G (\<G>_set (N - Red_F_\<G> N))\<close> 
        using Red_F_of_subset[OF not_red_map_in_map_not_red[of N]] by auto
      then have \<open>D \<in> Red_F_G (\<G>_set (N - N'))\<close>
        using N'_in_Red_F_N \<G>_subset[of "N - Red_F_\<G> N" "N - N'"]
        by (smt DiffE DiffI Red_F_of_subset subsetCE subsetI)
      then show ?thesis by blast
    next
      assume \<open>\<exists>E\<in>N - Red_F_\<G> N. E \<sqsubset> C \<and> D \<in> \<G>_F E\<close>
      then obtain E where 
        E_in: \<open>E\<in>N - Red_F_\<G> N\<close> and 
        E_prec_C: \<open>E \<sqsubset> C\<close> and 
        D_in: \<open>D \<in> \<G>_F E\<close> 
        by auto
      have \<open>E \<in> N - N'\<close> using E_in N'_in_Red_F_N by blast
      then show ?thesis using E_prec_C D_in by blast
    qed
  qed
qed

text \<open>lemma 13 in Uwe's notes\<close>
lemma Red_Inf_of_Red_F_subset_F: \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_Inf_\<G> N \<subseteq> Red_Inf_\<G> (N - N') \<close>
proof
  fix N N' \<iota>
  assume
    N'_in_Red_F_N: \<open>N' \<subseteq> Red_F_\<G> N\<close> and
    i_in_Red_Inf_N: \<open>\<iota> \<in> Red_Inf_\<G> N\<close>
  have i_in: \<open>\<iota> \<in> Inf_F\<close> using i_in_Red_Inf_N unfolding Red_Inf_\<G>_def by blast
  have \<open>\<forall>\<iota>' \<in> \<G>_Inf \<iota>. \<iota>' \<in> Red_Inf_G (\<G>_set N)\<close> using i_in_Red_Inf_N unfolding Red_Inf_\<G>_def by fast
  then have \<open>\<forall>\<iota>' \<in> \<G>_Inf \<iota>. \<iota>' \<in> Red_Inf_G (\<G>_set N - Red_F_G (\<G>_set N))\<close> 
    using Red_Inf_of_Red_F_subset by blast
  then have \<open>\<forall>\<iota>' \<in> \<G>_Inf \<iota>. \<iota>' \<in> Red_Inf_G (\<G>_set (N - Red_F_\<G> N))\<close>
    using Red_Inf_of_subset[OF not_red_map_in_map_not_red[of N]] by auto
  then have \<open>\<forall>\<iota>' \<in> \<G>_Inf \<iota>. \<iota>' \<in> Red_Inf_G (\<G>_set (N - N'))\<close>
    using  N'_in_Red_F_N by (smt Diff_iff Sup_set_def \<G>_subset calculus.Red_Inf_of_subset 
        calculus_axioms subset_iff)
  then show \<open>\<iota> \<in> Red_Inf_\<G> (N - N')\<close> unfolding Red_Inf_\<G>_def using i_in by blast
qed

text \<open>lemma 14 in Uwe's notes\<close>
lemma Red_Inf_of_Inf_to_N_F: 
  assumes
    i_in: \<open>\<iota> \<in> Inf_F\<close> and
    concl_i_in: \<open>concl_of \<iota> \<in> N\<close>
  shows
    \<open>\<iota> \<in> Red_Inf_\<G> N \<close>
proof -
  have \<open>\<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_F (concl_of \<iota>))\<close> using inf_map by simp
  moreover have \<open>Red_Inf_G (\<G>_F (concl_of \<iota>)) \<subseteq> Red_Inf_G (\<G>_set N)\<close>
    using concl_i_in Red_Inf_of_subset by blast
  ultimately show ?thesis using i_in unfolding Red_Inf_\<G>_def by simp
qed

text \<open>theorem 15 in Uwe's notes\<close>
sublocale lifted_calculus: calculus 
  where
    Bot = Bot_F and entails = entails_\<G> and Inf = Inf_F  and Red_Inf = Red_Inf_\<G> and Red_F = Red_F_\<G>
proof
  fix B N N' \<iota>
  show \<open>Red_Inf_\<G> N \<in> Pow Inf_F\<close> unfolding Red_Inf_\<G>_def by blast
  show \<open>B \<in> Bot_F \<Longrightarrow> N \<Turnstile>\<G> {B} \<Longrightarrow> N - Red_F_\<G> N \<Turnstile>\<G> {B}\<close> using Red_F_Bot_F by simp
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> N'\<close> using Red_F_of_subset_F by simp
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_Inf_\<G> N \<subseteq> Red_Inf_\<G> N'\<close> using Red_Inf_of_subset_F by simp
  show \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> (N - N')\<close> using Red_F_of_Red_F_subset_F by simp
  show \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_Inf_\<G> N \<subseteq> Red_Inf_\<G> (N - N')\<close> using Red_Inf_of_Red_F_subset_F by simp
  show \<open>\<iota> \<in> Inf_F \<and> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_Inf_\<G> N\<close> using Red_Inf_of_Inf_to_N_F by simp
qed

end

definition Empty_Order :: \<open>'f \<Rightarrow> 'f \<Rightarrow> bool\<close> where
  "Empty_Order C1 C2 \<equiv> False" 

locale lifting_equivalence_with_empty_order = g: redundancy_criterion_lifting Bot_G entails_G Inf_G Red_Inf_G Red_F_G Prec_F Bot_F Inf_F \<G>_F \<G>_Inf + q: redundancy_criterion_lifting Bot_G entails_G Inf_G Red_Inf_G Red_F_G Empty_Order Bot_F Inf_F \<G>_F \<G>_Inf
  for
    Bot_G :: \<open>'g set\<close> and
    entails_G :: \<open>'g set \<Rightarrow> 'g set \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    Inf_G :: \<open>'g inference set\<close> and
    Red_Inf_G :: \<open>'g set \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g set \<Rightarrow> 'g set\<close> and
    Prec_F :: \<open>'f \<Rightarrow> 'f \<Rightarrow> bool\<close> (infix "\<sqsubset>" 50) and
    Bot_F :: \<open>'f set\<close> and
    Inf_F :: \<open>'f inference set\<close> and
    \<G>_F :: \<open>'f \<Rightarrow> 'g set\<close> and
    \<G>_Inf :: \<open>'f inference \<Rightarrow> 'g inference set\<close>

sublocale redundancy_criterion_lifting \<subseteq> lifting_equivalence_with_empty_order
proof
  show "po_on Empty_Order UNIV" unfolding Empty_Order_def po_on_def by (simp add: transp_onI wfp_on_imp_irreflp_on)
  show "wfp_on Empty_Order UNIV" unfolding wfp_on_def Empty_Order_def by simp
  show "\<forall>B\<in>Bot_F. \<G>_F B \<noteq> {}" by (simp add: Bot_map_not_empty)
  show "\<forall>B\<in>Bot_F. \<G>_F B \<subseteq> Bot_G" by (simp add: Bot_map)
  fix \<iota>
  show "\<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_F (concl_of \<iota>))" by (simp add: inf_map)
qed

context lifting_equivalence_with_empty_order
begin

text "lemma 16 in Uwe's notes"
lemma "g.lifted_calculus.saturated N = q.lifted_calculus.saturated N" by standard

text "lemma 17 in Uwe's notes"
lemma static_empty_order_equiv_static: "static_refutational_complete_calculus Bot_F q.entails_\<G> Inf_F q.Red_Inf_\<G> q.Red_F_\<G> = static_refutational_complete_calculus Bot_F g.entails_\<G> Inf_F g.Red_Inf_\<G> g.Red_F_\<G>"
  unfolding static_refutational_complete_calculus_def by (rule iffI) (standard,(standard)[],simp)+
   
text "theorem 18 in Uwe's notes"
theorem "static_refutational_complete_calculus Bot_F q.entails_\<G> Inf_F q.Red_Inf_\<G> q.Red_F_\<G> = dynamic_refutational_complete_calculus Bot_F g.entails_\<G> Inf_F g.Red_Inf_\<G> g.Red_F_\<G> " (is "?static=?dynamic")
proof
  assume ?static
  then have static_general: "static_refutational_complete_calculus Bot_F g.entails_\<G> Inf_F g.Red_Inf_\<G> g.Red_F_\<G>" (is "?static_gen") using static_empty_order_equiv_static by simp
  interpret static_refutational_complete_calculus Bot_F g.entails_\<G> Inf_F g.Red_Inf_\<G> g.Red_F_\<G>
    using static_general .
  show "?dynamic" by standard 
next
  assume dynamic_gen: ?dynamic
  interpret dynamic_refutational_complete_calculus Bot_F g.entails_\<G> Inf_F g.Red_Inf_\<G> g.Red_F_\<G>
    using dynamic_gen .
  have "static_refutational_complete_calculus Bot_F g.entails_\<G> Inf_F g.Red_Inf_\<G> g.Red_F_\<G>"
    by standard
  then show "?static" using static_empty_order_equiv_static by simp
qed

end
end
