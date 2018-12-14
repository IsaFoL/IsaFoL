theory Splitting_Preliminaries
  imports
    Ordered_Resolution_Prover.Clausal_Logic
    "../Saturation_Framework/Saturation_Framework_Preliminaries"
begin

locale compact_calculus = calculus Bot for Bot :: "'f set" +
  assumes
    Red_F_compact: "C \<in> Red_F N \<Longrightarrow> \<exists>N' \<subseteq> N. finite N' \<and> C \<in> Red_F N'"
begin

end

end
