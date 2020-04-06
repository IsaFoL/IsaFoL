(*  Title:       Calculi of the Saturation Framework
 *  Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2020 *)

theory Soundness_Related
  imports Consequence_Relations_and_Inference_Systems
begin

locale sound_inference_system = inference_system + consequence_relation +
  assumes
    soundness: \<open>\<iota> \<in> Inf \<Longrightarrow> set (prems_of \<iota>) \<Turnstile> {concl_of \<iota>}\<close>

end