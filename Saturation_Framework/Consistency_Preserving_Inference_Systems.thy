(*  Title:       Consistency-Preserving Inference Systems
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017, 2020
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

theory Consistency_Preserving_Inference_Systems
  imports Saturation_Framework.Consequence_Relations_and_Inference_Systems
begin

locale consist_preserving_inference_system =
  inference_system + consequence_relation +
  assumes
    sound: \<open>\<not> N \<Turnstile> Bot \<Longrightarrow> \<not> N \<union> concl_of ` Inf_from N \<Turnstile> Bot\<close>
begin

end

end
