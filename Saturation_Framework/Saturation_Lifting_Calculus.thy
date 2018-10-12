theory Saturation_Lifting_Calculus
imports "Saturation_Framework.Saturation_Framework_Preliminaries"
begin

locale lifting_calculus = grounding_function Bot_F entails_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G Inf_F \<G>_F \<G>_Inf
  for
    Bot_F :: \<open>'f set\<close> and
    entails_F ::  \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix "\<Turnstile>F" 50) and
    Bot_G :: \<open>'g set\<close> and
    entails_G ::  \<open>'g set  \<Rightarrow> 'g set  \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    Inf_G ::  \<open>'g inference set\<close> and
    Red_Inf_G :: \<open>'g set \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g set \<Rightarrow> 'g set\<close> and
    Inf_F :: \<open>'f inference set\<close> and
    \<G>_F :: \<open>'f \<Rightarrow> 'g set\<close> and
    \<G>_Inf :: \<open>'f inference \<Rightarrow> 'g inference set\<close>
  + assumes \<G>_entails: \<open>N \<Turnstile>F M \<longleftrightarrow> \<G>_set N \<Turnstile>G \<G>_set M\<close>
begin

fun Red_F_F :: \<open>'f set \<Rightarrow> 'f set\<close> where
\<open>Red_F_F N = {C. \<G>_F C \<subseteq> Red_F_G (\<G>_set N)}\<close>

fun Red_Inf_F :: \<open>'f set \<Rightarrow> 'f inference set\<close> where
\<open>Red_Inf_F N = {\<iota>. \<iota> \<in> Inf_F \<and> \<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_set N)}\<close>

lemma \<G>_refut: \<open>(\<exists>B. B \<in> Bot_F \<and> N \<Turnstile>F {B}) \<longleftrightarrow> (\<exists>C. C \<in>Bot_G \<and> \<G>_set N \<Turnstile>G {C})\<close>
proof
  show \<open>\<exists>B. B \<in> Bot_F \<and> N \<Turnstile>F {B} \<Longrightarrow> \<exists>C. C \<in> Bot_G \<and> \<G>_set N \<Turnstile>G {C}\<close>
  proof -
    assume "\<exists>B. B \<in> Bot_F \<and> N \<Turnstile>F {B}"
    then have "\<exists>B. B \<in> Bot_F \<and> \<G>_set N \<Turnstile>G \<G>_F B" using \<G>_entails by auto
    then obtain B C where "B \<in> Bot_F" and "\<G>_set N \<Turnstile>G \<G>_F B" and "C \<in> \<G>_F B" using Bot_map_not_empty by blast
    then have "C \<in> Bot_G \<and> \<G>_set N \<Turnstile>G {C}" using Bot_map_subset and g.entail_set_all_formulas by blast
    then show "\<exists>C. C \<in> Bot_G \<and> \<G>_set N \<Turnstile>G {C}" by auto
  qed
next
  show \<open>\<exists>C. C \<in> Bot_G \<and> \<G>_set N \<Turnstile>G {C} \<Longrightarrow> \<exists>B. B \<in> Bot_F \<and> N \<Turnstile>F {B}\<close> sorry
  (* need to assume surjectivity of \<G>_F on Bot_F  *)
qed


sublocale calculus_F: calculus Bot_F entails_F Inf_F Red_Inf_F Red_F_F
proof
  show \<open>Red_Inf_F N \<subseteq> Inf_F\<close> for N by auto
next
  show \<open>B \<in> Bot_F \<Longrightarrow> N \<Turnstile>F {B} \<Longrightarrow> (N - Red_F_F N) \<Turnstile>F {B}\<close> for B N
  proof -
    assume \<open>B \<in> Bot_F\<close> and \<open>N \<Turnstile>F {B}\<close>
    then obtain C where \<open>\<G>_set N \<Turnstile>G {C}\<close> and bot_C: \<open>C \<in> Bot_G\<close> using \<G>_refut by auto
    then have \<open>\<G>_set N - Red_F_G (\<G>_set N) \<Turnstile>G {C}\<close> using g.Red_F_Bot by auto
    moreover have \<open>\<G>_set N - Red_F_G (\<G>_set N) \<subseteq> \<G>_set (N - Red_F_F N)\<close> by auto
    ultimately have \<open>\<G>_set (N - Red_F_F N) \<Turnstile>G {C}\<close> by (meson g.subset_entailed g.entails_trans)
    with bot_C obtain D where \<open>N - Red_F_F N \<Turnstile>F {D}\<close> and \<open>D \<in> Bot_F\<close> using \<G>_refut by auto
    then show \<open>(N - Red_F_F N) \<Turnstile>F {B}\<close> using f.bot_implies_all f.entails_trans by blast
  qed
next
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_F_F N \<subseteq> Red_F_F N'\<close> for N N'
  proof -
    assume \<open>N \<subseteq> N'\<close>
    then have \<open>\<G>_set N \<subseteq> \<G>_set N'\<close> by auto
    then have \<open>Red_F_G (\<G>_set N) \<subseteq> Red_F_G (\<G>_set N')\<close> using g.Red_F_of_subset by auto
    then show \<open>Red_F_F N \<subseteq> Red_F_F N'\<close> by auto
  qed
next
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_Inf_F N \<subseteq> Red_Inf_F N'\<close> for N N'
  proof -
    assume \<open>N \<subseteq> N'\<close>
    then have \<open>\<G>_set N \<subseteq> \<G>_set N'\<close> by auto
    then have \<open>Red_Inf_G (\<G>_set N) \<subseteq> Red_Inf_G (\<G>_set N')\<close> using g.Red_Inf_of_subset by auto
    then show \<open>Red_Inf_F N \<subseteq> Red_Inf_F N'\<close> by auto
  qed
next
  show \<open>N' \<subseteq> Red_F_F N \<Longrightarrow> Red_F_F N \<subseteq> Red_F_F (N - N')\<close> for N N'
  proof -
    assume \<open>N' \<subseteq> Red_F_F N\<close>
    then have \<open>\<G>_set N' \<subseteq> Red_F_G (\<G>_set N)\<close> by auto
    then have \<open>Red_F_G (\<G>_set N) \<subseteq> Red_F_G (\<G>_set N - \<G>_set N')\<close> using g.Red_F_of_Red_F_subset by auto
    also have \<open>\<G>_set N - \<G>_set N' \<subseteq> \<G>_set (N - N')\<close> by fastforce
    then have \<open>Red_F_G (\<G>_set N - \<G>_set N') \<subseteq> Red_F_G (\<G>_set (N - N'))\<close> using g.Red_F_of_subset by auto
    finally show \<open>Red_F_F N \<subseteq> Red_F_F (N - N')\<close> by auto
  qed
next
  show \<open>N' \<subseteq> Red_F_F N \<Longrightarrow> Red_Inf_F N \<subseteq> Red_Inf_F (N - N')\<close> for N N'
  proof -
    assume \<open>N' \<subseteq> Red_F_F N\<close>
    then have \<open>\<G>_set N' \<subseteq> Red_F_G (\<G>_set N)\<close> by auto
    then have \<open>Red_Inf_G (\<G>_set N) \<subseteq> Red_Inf_G (\<G>_set N - \<G>_set N')\<close> using g.Red_Inf_of_Red_F_subset by auto
    also have \<open>\<G>_set N - \<G>_set N' \<subseteq> \<G>_set (N - N')\<close> by fastforce
    then have \<open>Red_Inf_G (\<G>_set N - \<G>_set N') \<subseteq> Red_Inf_G (\<G>_set (N - N'))\<close> using g.Red_Inf_of_subset by auto
    finally show \<open>Red_Inf_F N \<subseteq> Red_Inf_F (N - N')\<close> by auto
  qed
next
  show \<open>\<iota> \<in> Inf_F \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_Inf_F N\<close> for \<iota> N
  proof -
    assume 1: \<open>\<iota> \<in> Inf_F\<close> and \<open>concl_of \<iota> \<in> N\<close>
    then have \<open>\<G>_F (concl_of \<iota>) \<subseteq> \<G>_set N\<close> by auto
    then have \<open>Red_Inf_G (\<G>_F (concl_of \<iota>)) \<subseteq> Red_Inf_G (\<G>_set N)\<close> using g.Red_Inf_of_subset by auto
    moreover have \<open>\<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_F (concl_of \<iota>))\<close> by (simp add: inf_map)
    ultimately have \<open>\<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_set N)\<close> by auto
    then show \<open>\<iota> \<in> Red_Inf_F N\<close> by auto
  qed
qed

end

end