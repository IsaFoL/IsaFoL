(*  Title:       Nonground_Calculus_Lifting
    Author:      Simon Robillard <simon.robillard at chalmers.se>, 2018
*)

theory Nonground_Calculus_Lifting
  imports Saturation_Framework_Preliminaries 
begin

locale nonground_static_refutational_complete_calculus = grounding_function Bot_F entails_sound_F Inf_F Bot_G entails_sound_G Inf_G entails_comp_G Red_Inf_G Red_F_G +
  static_refutational_complete_calculus Bot_G entails_sound_G Inf_G entails_comp_G Red_Inf_G Red_F_G
  for
    Bot_F :: \<open>'f set\<close> and
    entails_sound_F ::  \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix "\<TTurnstile>F" 50) and
    Inf_F :: \<open>'f inference set\<close> and
    Bot_G :: \<open>'g set\<close> and
    entails_sound_G ::  \<open>'g set  \<Rightarrow> 'g set  \<Rightarrow> bool\<close> (infix "\<TTurnstile>G" 50) and
    Inf_G ::  \<open>'g inference set\<close> and
    entails_comp_G ::  \<open>'g set  \<Rightarrow> 'g set  \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    Red_Inf_G :: \<open>'g set \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g set \<Rightarrow> 'g set\<close>
  + assumes Ground_inf_liftable_or_redundant: \<open>\<iota> \<in> Ground.Inf_from (\<G>_set N) \<Longrightarrow> \<iota> \<in> Red_Inf_G (\<G>_set N) \<or> (\<exists>\<kappa>. \<kappa> \<in> Non_ground.Inf_from N \<and> \<iota> \<in> \<G>_Inf \<kappa>)\<close>
begin

fun entails_comp_F :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix "\<Turnstile>F" 50) where
\<open>N \<Turnstile>F M \<longleftrightarrow> \<G>_set N \<Turnstile>G \<G>_set M\<close>

lemma \<G>_refut: \<open>B \<in> Bot_F \<Longrightarrow> N \<Turnstile>F {B} \<Longrightarrow> \<exists>C. C \<in>Bot_G \<and> \<G>_set N \<Turnstile>G {C}\<close>
proof -
  assume B_bot: \<open>B \<in> Bot_F\<close> and \<open>N \<Turnstile>F {B}\<close>
  then have B_entailed: \<open>\<G>_set N \<Turnstile>G \<G>_F B\<close> by auto
  then obtain C where C_ground: \<open>C \<in> \<G>_F B\<close> and C_bot: \<open>C \<in> Bot_G\<close> using B_bot Bot_map Bot_map_not_empty by blast
  then have "\<G>_set N \<Turnstile>G {C}" using B_entailed C_ground Ground.entail_set_all_formulas by blast
  then show "\<exists>C. C \<in> Bot_G \<and> \<G>_set N \<Turnstile>G {C}" using C_bot by auto
qed

sublocale consequence_relation Bot_F entails_comp_F
proof
  show \<open>B\<in>Bot_F \<Longrightarrow> {B} \<Turnstile>F N1\<close> for B N1
  proof -
    assume \<open>B \<in> Bot_F\<close>
    then obtain C where \<open>C \<in> \<G>_F B\<close> and \<open>C \<in> Bot_G\<close> using Bot_map Bot_map_not_empty by blast
    then have \<open>\<G>_F B \<Turnstile>G {C}\<close> and \<open>{C} \<Turnstile>G \<G>_set N1\<close> using Ground.subset_entailed [of \<open>{C}\<close> \<open>\<G>_F B\<close>] Ground.bot_implies_all by auto
    then show \<open>{B} \<Turnstile>F N1\<close> using Ground.entails_trans [where ?N2.0=\<open>{C}\<close>] by auto
  qed
next
  show \<open>N2 \<subseteq> N1 \<Longrightarrow> N1 \<Turnstile>F N2\<close> for N1 N2 using Ground.subset_entailed [of \<open>\<G>_set N2\<close> \<open>\<G>_set N1\<close>] by auto
next
  show \<open>\<forall>C\<in>N2. N1 \<Turnstile>F {C} \<Longrightarrow> N1 \<Turnstile>F N2\<close> for N1 N2
  proof -
    assume \<open>\<forall>C \<in> N2. N1 \<Turnstile>F {C}\<close>
    then have \<open>\<forall>C \<in> N2. \<G>_set N1 \<Turnstile>G \<G>_F C\<close> by auto
    then have \<open>\<G>_set N1 \<Turnstile>G \<G>_set N2\<close> using Ground.entail_set_all_formulas by blast
    then show \<open>N1 \<Turnstile>F N2\<close> by auto
  qed
next
  show \<open>N1 \<Turnstile>F N2 \<Longrightarrow> N2 \<Turnstile>F N3 \<Longrightarrow> N1 \<Turnstile>F N3\<close> for N1 N2 N3 using Ground.entails_trans [where ?N2.0=\<open>\<G>_set N2\<close>] by auto
qed

fun Red_F_F :: \<open>'f set \<Rightarrow> 'f set\<close> where
\<open>Red_F_F N = {C. \<G>_F C \<subseteq> Red_F_G (\<G>_set N)}\<close>

fun Red_Inf_F :: \<open>'f set \<Rightarrow> 'f inference set\<close> where
\<open>Red_Inf_F N = {\<iota>. \<iota> \<in> Inf_F \<and> \<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_set N)}\<close>

sublocale calculus Bot_F entails_sound_F Inf_F entails_comp_F Red_Inf_F Red_F_F
proof
  show \<open>Red_Inf_F N \<subseteq> Inf_F\<close> for N by auto
next
  show \<open>B \<in> Bot_F \<Longrightarrow> N \<Turnstile>F {B} \<Longrightarrow> (N - Red_F_F N) \<Turnstile>F {B}\<close> for B N
  proof -
    assume \<open>B \<in> Bot_F\<close> and \<open>N \<Turnstile>F {B}\<close>
    then obtain C where \<open>\<G>_set N \<Turnstile>G {C}\<close> and C_bot: \<open>C \<in> Bot_G\<close> using \<G>_refut by auto
    then have \<open>\<G>_set N - Red_F_G (\<G>_set N) \<Turnstile>G {C}\<close> using Ground.Red_F_Bot by auto
    moreover have \<open>\<G>_set N - Red_F_G (\<G>_set N) \<subseteq> \<G>_set (N - Red_F_F N)\<close> by auto
    ultimately have \<open>\<G>_set (N - Red_F_F N) \<Turnstile>G {C}\<close> by (meson Ground.subset_entailed Ground.entails_trans)
    then have \<open>\<G>_set (N - Red_F_F N) \<Turnstile>G N'\<close> for N' using C_bot Ground.bot_implies_all Ground.entails_trans by blast
    then show \<open>(N - Red_F_F N) \<Turnstile>F {B}\<close> by auto 
  qed
next
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_F_F N \<subseteq> Red_F_F N'\<close> for N N'
  proof -
    assume \<open>N \<subseteq> N'\<close>
    then have \<open>\<G>_set N \<subseteq> \<G>_set N'\<close> by auto
    then have \<open>Red_F_G (\<G>_set N) \<subseteq> Red_F_G (\<G>_set N')\<close> using Ground.Red_F_of_subset by auto
    then show \<open>Red_F_F N \<subseteq> Red_F_F N'\<close> by auto
  qed
next
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_Inf_F N \<subseteq> Red_Inf_F N'\<close> for N N'
  proof -
    assume \<open>N \<subseteq> N'\<close>
    then have \<open>\<G>_set N \<subseteq> \<G>_set N'\<close> by auto
    then have \<open>Red_Inf_G (\<G>_set N) \<subseteq> Red_Inf_G (\<G>_set N')\<close> using Ground.Red_Inf_of_subset by auto
    then show \<open>Red_Inf_F N \<subseteq> Red_Inf_F N'\<close> by auto
  qed
next
  show \<open>N' \<subseteq> Red_F_F N \<Longrightarrow> Red_F_F N \<subseteq> Red_F_F (N - N')\<close> for N N'
  proof -
    assume \<open>N' \<subseteq> Red_F_F N\<close>
    then have \<open>\<G>_set N' \<subseteq> Red_F_G (\<G>_set N)\<close> by auto
    then have \<open>Red_F_G (\<G>_set N) \<subseteq> Red_F_G (\<G>_set N - \<G>_set N')\<close> using Ground.Red_F_of_Red_F_subset by auto
    also have \<open>\<G>_set N - \<G>_set N' \<subseteq> \<G>_set (N - N')\<close> by fastforce
    then have \<open>Red_F_G (\<G>_set N - \<G>_set N') \<subseteq> Red_F_G (\<G>_set (N - N'))\<close> using Ground.Red_F_of_subset by auto
    finally show \<open>Red_F_F N \<subseteq> Red_F_F (N - N')\<close> by auto
  qed
next
  show \<open>N' \<subseteq> Red_F_F N \<Longrightarrow> Red_Inf_F N \<subseteq> Red_Inf_F (N - N')\<close> for N N'
  proof -
    assume \<open>N' \<subseteq> Red_F_F N\<close>
    then have \<open>\<G>_set N' \<subseteq> Red_F_G (\<G>_set N)\<close> by auto
    then have \<open>Red_Inf_G (\<G>_set N) \<subseteq> Red_Inf_G (\<G>_set N - \<G>_set N')\<close> using Ground.Red_Inf_of_Red_F_subset by auto
    also have \<open>\<G>_set N - \<G>_set N' \<subseteq> \<G>_set (N - N')\<close> by fastforce
    then have \<open>Red_Inf_G (\<G>_set N - \<G>_set N') \<subseteq> Red_Inf_G (\<G>_set (N - N'))\<close> using Ground.Red_Inf_of_subset by auto
    finally show \<open>Red_Inf_F N \<subseteq> Red_Inf_F (N - N')\<close> by auto
  qed
next
  show \<open>\<iota> \<in> Inf_F \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_Inf_F N\<close> for \<iota> N
  proof -
    assume \<iota>_Inf_F: \<open>\<iota> \<in> Inf_F\<close> and \<open>concl_of \<iota> \<in> N\<close>
    then have \<open>\<G>_F (concl_of \<iota>) \<subseteq> \<G>_set N\<close> by auto
    then have \<open>Red_Inf_G (\<G>_F (concl_of \<iota>)) \<subseteq> Red_Inf_G (\<G>_set N)\<close> using Ground.Red_Inf_of_subset by auto
    moreover have \<open>\<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_F (concl_of \<iota>))\<close> by (simp add: \<iota>_Inf_F inf_map)
    ultimately have \<open>\<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_set N)\<close> by auto
    with \<iota>_Inf_F show \<open>\<iota> \<in> Red_Inf_F N\<close> by auto
  qed
qed

sublocale static_refutational_complete_calculus Bot_F entails_sound_F Inf_F entails_comp_F Red_Inf_F Red_F_F
proof
  show \<open>B \<in> Bot_F \<Longrightarrow> saturated N \<Longrightarrow> N \<Turnstile>F {B} \<Longrightarrow> \<exists>B'\<in>Bot_F. B' \<in> N\<close> for B N
  proof -
    assume
      B_bot: \<open>B \<in> Bot_F\<close> and
      saturated_nonground: \<open>saturated N\<close> and
      B_entailed: \<open>N \<Turnstile>F {B}\<close>
      have saturated_ground: \<open>Ground.saturated (\<G>_set N)\<close> unfolding Ground.saturated_def
      proof -
        show \<open>Ground.Inf_from (\<G>_set N) \<subseteq> Red_Inf_G (\<G>_set N)\<close>
      proof
        show \<open>\<iota> \<in> Ground.Inf_from (\<G>_set N) \<Longrightarrow> \<iota> \<in> Red_Inf_G (\<G>_set N)\<close> for \<iota>
        proof -
          assume \<open>\<iota> \<in> Ground.Inf_from (\<G>_set N)\<close>
          then consider (a) \<open>\<iota> \<in> Red_Inf_G (\<G>_set N)\<close>
                      | (b) \<open>\<exists>\<kappa>. \<kappa> \<in> Non_ground.Inf_from N \<and> \<iota> \<in> \<G>_Inf \<kappa>\<close> 
            using Ground_inf_liftable_or_redundant by auto
          then show \<open>\<iota> \<in> Red_Inf_G (\<G>_set N)\<close>
          proof cases
            case a
            then show ?thesis .
          next
            case b
            then obtain \<kappa> where \<open>\<kappa> \<in> Inf_F\<close> and \<open>set (prems_of \<kappa>) \<subseteq> N\<close> and \<open>\<iota> \<in> \<G>_Inf \<kappa>\<close>
              unfolding Non_ground.Inf_from_def by auto
            then show \<open>\<iota> \<in> Red_Inf_G (\<G>_set N)\<close>
              using saturated_nonground unfolding saturated_def Non_ground.Inf_from_def by auto
          qed
        qed
      qed
    qed
    from B_bot and B_entailed and \<G>_refut obtain C where \<open>C \<in> Bot_G\<close> and \<open>\<G>_set N \<Turnstile>G {C}\<close> by auto
    with saturated_ground obtain C' where \<open>C' \<in> Bot_G\<close> and \<open>C' \<in> \<G>_set N\<close> using static_refutational_complete by blast
    then obtain B' where \<open>C' \<in> \<G>_F B'\<close> and \<open>B' \<in> N\<close> and \<open>B' \<in> Bot_F\<close> using Bot_cond by auto
    then show \<open>\<exists>B' \<in> Bot_F. B' \<in> N\<close> by auto
  qed
qed

end

end