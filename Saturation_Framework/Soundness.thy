(*  Title:       Soundness
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2020
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2020
*)

section \<open>Soundness\<close>

theory Soundness
  imports Consistency_Preservation
begin

text \<open>
Although consistency-preservation usually suffices, soundness is a more precise concept and is
sometimes useful.
\<close>

locale sound_inference_system = inference_system + consequence_relation +
  assumes
    sound: \<open>\<iota> \<in> Inf \<Longrightarrow> set (prems_of \<iota>) \<Turnstile> {concl_of \<iota>}\<close>
begin

lemma Inf_consist_preserving:
  assumes n_cons: "\<not> N \<Turnstile> Bot"
  shows "\<not> N \<union> concl_of ` Inf_from N \<Turnstile> Bot"
proof -
  have "N \<Turnstile> concl_of ` Inf_from N"
    using sound unfolding Inf_from_def image_def Bex_def mem_Collect_eq
    by (smt all_formulas_entailed entails_trans mem_Collect_eq subset_entailed)
  then show ?thesis
    using n_cons entails_trans_strong by blast
qed

end

end
