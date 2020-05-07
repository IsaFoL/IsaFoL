(*  Title:       Soundness Results
 *  Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2020
 *  Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2020 *)

theory Soundness
  imports Consistency_Preservation
begin

locale sound_calculus_with_red_crit = calculus_with_red_crit +
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
