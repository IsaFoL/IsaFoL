(*  Title:       Prover_Completeness_Lifting
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2019
*)

theory Prover_Completeness_Lifting
imports Dynamic_Completeness_Lifting
begin

subsection \<open>Adding labels\<close>

locale labeled_lifting_w_wf_ord_family = lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf Prec_F
  for
    Bot_F :: "'f set" and
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    entails_G :: "'g set \<Rightarrow> 'g set \<Rightarrow> bool"  (infix "\<Turnstile>G" 50) and
    Inf_G :: "'g inference set" and
    Red_Inf_G :: "'g set \<Rightarrow> 'g inference set" and
    Red_F_G :: "'g set \<Rightarrow> 'g set" and
    \<G>_F :: "'f \<Rightarrow> 'g set" and
    \<G>_Inf :: "'f inference \<Rightarrow> 'g inference set" and
    Prec_F :: "'g \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool"  (infix "\<sqsubset>" 50)
  + fixes
    l :: \<open>'l itself\<close> and
    Inf_FL :: \<open>('f \<times> 'l) inference set\<close>
  assumes
    Inf_F_to_Inf_FL: \<open>\<iota>\<^sub>F \<in> Inf_F \<Longrightarrow> length (Ll :: 'l list) = length (prems_of \<iota>\<^sub>F) \<Longrightarrow> \<exists>L0. Infer (zip (prems_of \<iota>\<^sub>F) Ll) (concl_of \<iota>\<^sub>F, L0) \<in> Inf_FL\<close> and
    Inf_FL_to_Inf_F: \<open>\<iota>\<^sub>F\<^sub>L \<in> Inf_FL \<Longrightarrow> Infer (map fst (prems_of \<iota>\<^sub>F\<^sub>L)) (fst (concl_of \<iota>\<^sub>F\<^sub>L)) \<in> Inf_F\<close>
begin

definition to_F :: \<open>('f \<times> 'l) inference \<Rightarrow> 'f inference\<close> where
  \<open>to_F \<iota>\<^sub>F\<^sub>L = Infer (map fst (prems_of \<iota>\<^sub>F\<^sub>L)) (fst (concl_of \<iota>\<^sub>F\<^sub>L))\<close>

text \<open>The set FL is implicitly defined as \<^term>\<open>UNIV::('f\<times>'l) set\<close> and the function \<^term>\<open>proj_1\<close> is
  implicitly defined as \<^term>\<open>(`) fst\<close>.\<close>
definition Bot_FL :: \<open>('f \<times> 'l) set\<close> where \<open>Bot_FL = Bot_F \<times> UNIV\<close>

definition \<G>_F_L :: \<open>('f \<times> 'l) \<Rightarrow> 'g set\<close> where \<open>\<G>_F_L CL = \<G>_F (fst CL)\<close>

definition \<G>_Inf_L :: \<open>('f \<times> 'l) inference \<Rightarrow> 'g inference set\<close> where \<open>\<G>_Inf_L \<iota>\<^sub>F\<^sub>L = \<G>_Inf (to_F \<iota>\<^sub>F\<^sub>L)\<close>

(* definition entails_sound_FL :: \<open>('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> bool\<close> (infix "|\<approx>FL" 50) where \<open>CL1 |\<approx>FL
CL2 \<equiv> fst ` CL1 |\<approx>F fst ` CL2\<close> *)

text \<open>Lemma 48 from the technical report\<close>
sublocale labeled_standard_lifting: standard_lifting
  where
    Bot_F = Bot_FL and
    Inf_F = Inf_FL and
    \<G>_F = \<G>_F_L and
    \<G>_Inf = \<G>_Inf_L
proof
  show "Bot_FL \<noteq> {}"
    unfolding Bot_FL_def using Bot_F_not_empty by simp
next
  show "B\<in>Bot_FL \<Longrightarrow> \<G>_F_L B \<noteq> {}" for B
    unfolding \<G>_F_L_def Bot_FL_def using Bot_map_not_empty by auto
next
  show "B\<in>Bot_FL \<Longrightarrow> \<G>_F_L B \<subseteq> Bot_G" for B
    unfolding \<G>_F_L_def Bot_FL_def using Bot_map by force
next
  fix CL
  show "\<G>_F_L CL \<inter> Bot_G \<noteq> {} \<longrightarrow> CL \<in> Bot_FL"
    unfolding \<G>_F_L_def Bot_FL_def using Bot_cond by (metis SigmaE UNIV_I UNIV_Times_UNIV mem_Sigma_iff prod.sel(1))
next
  fix \<iota>
  assume \<open>\<iota> \<in> Inf_FL\<close>
  then show "\<G>_Inf_L \<iota> \<subseteq> Red_Inf_G (\<G>_F_L (concl_of \<iota>))"
    unfolding \<G>_Inf_L_def \<G>_F_L_def to_F_def using inf_map Inf_FL_to_Inf_F by fastforce
qed

definition Labeled_Empty_Order :: \<open> ('f \<times> 'l) \<Rightarrow> ('f \<times> 'l) \<Rightarrow> bool\<close> where
  "Labeled_Empty_Order C1 C2 \<equiv> False" 

sublocale labeled_lifting_w_empty_ord_family : lifting_with_wf_ordering_family Bot_FL Inf_FL Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F_L \<G>_Inf_L "\<lambda>g. Labeled_Empty_Order" 
proof
  show "po_on Labeled_Empty_Order UNIV" unfolding Labeled_Empty_Order_def po_on_def by (simp add: transp_onI wfp_on_imp_irreflp_on)
  show "wfp_on Labeled_Empty_Order UNIV" unfolding wfp_on_def Labeled_Empty_Order_def by simp
qed

notation "labeled_standard_lifting.entails_\<G>" (infix "\<Turnstile>\<G>L" 50)

text \<open>Lemma 49 from the technical report\<close>
lemma labeled_entailment_lifting: "NL1 \<Turnstile>\<G>L NL2 \<longleftrightarrow> fst ` NL1 \<Turnstile>\<G> fst ` NL2"
  unfolding labeled_standard_lifting.entails_\<G>_def \<G>_F_L_def entails_\<G>_def by auto

lemma subset_fst: "A \<subseteq> fst ` AB \<Longrightarrow> \<forall>x \<in> A. \<exists>y. (x,y) \<in> AB" by fastforce

lemma red_inf_impl: "\<iota> \<in> labeled_lifting_w_empty_ord_family.Red_Inf_\<G> NL \<Longrightarrow> to_F \<iota> \<in> Red_Inf_\<G> (fst ` NL)"
  unfolding labeled_lifting_w_empty_ord_family.Red_Inf_\<G>_def Red_Inf_\<G>_def \<G>_Inf_L_def \<G>_F_L_def to_F_def
  using Inf_FL_to_Inf_F by auto

text \<open>lemma 50 from the technical report\<close>
lemma labeled_saturation_lifting:
  "labeled_lifting_w_empty_ord_family.lifted_calculus_with_red_crit.saturated NL \<Longrightarrow>
    empty_order_lifting.lifted_calculus_with_red_crit.saturated (fst ` NL)"
  unfolding labeled_lifting_w_empty_ord_family.lifted_calculus_with_red_crit.saturated_def
    empty_order_lifting.lifted_calculus_with_red_crit.saturated_def
    labeled_standard_lifting.Non_ground.Inf_from_def Non_ground.Inf_from_def
proof clarify
  fix \<iota>
  assume
    subs_Red_Inf: "{\<iota> \<in> Inf_FL. set (prems_of \<iota>) \<subseteq> NL} \<subseteq> labeled_lifting_w_empty_ord_family.Red_Inf_\<G> NL" and
    i_in: "\<iota> \<in> Inf_F" and
    i_prems: "set (prems_of \<iota>) \<subseteq> fst ` NL"
  define Lli where "Lli i \<equiv> (SOME x. ((prems_of \<iota>)!i,x) \<in> NL)" for i
  have [simp]:"((prems_of \<iota>)!i,Lli i) \<in> NL" if "i < length (prems_of \<iota>)" for i
    using that subset_fst[OF i_prems] unfolding Lli_def by (meson nth_mem someI_ex)
  define Ll where "Ll \<equiv> map Lli [0..<length (prems_of \<iota>)]"
  have Ll_length: "length Ll = length (prems_of \<iota>)" unfolding Ll_def by auto
    (* "\<exists>L0. Infer (zip (prems_of \<iota>) Ll) (concl_of \<iota>, L0) \<in> Inf_FL" and *)
  have subs_NL: "set (zip (prems_of \<iota>) Ll) \<subseteq> NL" unfolding Ll_def by (auto simp:in_set_zip)
  obtain L0 where L0: "Infer (zip (prems_of \<iota>) Ll) (concl_of \<iota>, L0) \<in> Inf_FL"
    using Inf_F_to_Inf_FL[OF i_in Ll_length] ..
  define \<iota>_FL where "\<iota>_FL = Infer (zip (prems_of \<iota>) Ll) (concl_of \<iota>, L0)"
  then have "set (prems_of \<iota>_FL) \<subseteq> NL" using subs_NL by simp
  then have "\<iota>_FL \<in> {\<iota> \<in> Inf_FL. set (prems_of \<iota>) \<subseteq> NL}" unfolding \<iota>_FL_def using L0 by blast
  then have "\<iota>_FL \<in> labeled_lifting_w_empty_ord_family.Red_Inf_\<G> NL" using subs_Red_Inf by fast
  moreover have "\<iota> = to_F \<iota>_FL" unfolding to_F_def \<iota>_FL_def using Ll_length by (cases \<iota>) auto
  ultimately show "\<iota> \<in> Red_Inf_\<G> (fst ` NL)" by (auto intro:red_inf_impl)
qed

text "lemma 51 from the technical report"
lemma "static_refutational_complete_calculus Bot_F Inf_F (\<Turnstile>\<G>) Red_Inf_\<G> Red_F_\<G> \<Longrightarrow> static_refutational_complete_calculus Bot_FL Inf_FL (\<Turnstile>\<G>L) labeled_lifting_w_empty_ord_family.Red_Inf_\<G> labeled_lifting_w_empty_ord_family.Red_F_\<G>"
  unfolding static_refutational_complete_calculus_def
proof (rule conjI impI; clarify)
  interpret calculus_with_red_crit Bot_FL Inf_FL labeled_standard_lifting.entails_\<G> labeled_lifting_w_empty_ord_family.Red_Inf_\<G> labeled_lifting_w_empty_ord_family.Red_F_\<G> by (simp add: labeled_lifting_w_empty_ord_family.lifted_calculus_with_red_crit.calculus_with_red_crit_axioms)
  show "calculus_with_red_crit Bot_FL Inf_FL (\<Turnstile>\<G>L) labeled_lifting_w_empty_ord_family.Red_Inf_\<G> labeled_lifting_w_empty_ord_family.Red_F_\<G>" by standard
next
  assume
    calc: "calculus_with_red_crit Bot_F Inf_F (\<Turnstile>\<G>) Red_Inf_\<G> Red_F_\<G>" and
    static: "static_refutational_complete_calculus_axioms Bot_F Inf_F (\<Turnstile>\<G>) Red_Inf_\<G>"
  show "static_refutational_complete_calculus_axioms Bot_FL Inf_FL (\<Turnstile>\<G>L)
    labeled_lifting_w_empty_ord_family.Red_Inf_\<G>"
    unfolding static_refutational_complete_calculus_axioms_def
  proof (intro conjI impI allI)
    fix Bl :: \<open>'f \<times> 'l\<close> and Nl :: \<open>('f \<times> 'l) set\<close>
    assume 
      Bl_in: \<open>Bl \<in> Bot_FL\<close> and
      Nl_sat: \<open>labeled_lifting_w_empty_ord_family.empty_order_lifting.lifted_calculus_with_red_crit.saturated Nl\<close> and
      Nl_entails_Bl: \<open>Nl \<Turnstile>\<G>L {Bl}\<close>
    have static_axioms: "B \<in> Bot_F \<longrightarrow> empty_order_lifting.lifted_calculus_with_red_crit.saturated N \<longrightarrow>
      N \<Turnstile>\<G> {B} \<longrightarrow> (\<exists>B'\<in>Bot_F. B' \<in> N)" for B N
      using static[unfolded static_refutational_complete_calculus_axioms_def] by fast
    define B where "B = fst Bl"
    have B_in: "B \<in> Bot_F" using Bl_in Bot_FL_def B_def SigmaE by force
    define N where "N = fst ` Nl"
    have N_sat: "empty_order_lifting.lifted_calculus_with_red_crit.saturated N"
      using N_def Nl_sat labeled_saturation_lifting by blast 
    have N_entails_B: "N \<Turnstile>\<G> {B}" using Nl_entails_Bl unfolding labeled_entailment_lifting N_def B_def by force
    have "\<exists>B' \<in> Bot_F. B' \<in> N" using B_in N_sat N_entails_B static_axioms[of B N] by blast
    then obtain B' where in_Bot: "B' \<in> Bot_F" and in_N: "B' \<in> N" by force
    then have "B' \<in> fst ` Bot_FL" unfolding Bot_FL_def by fastforce
    obtain Bl' where in_Nl: "Bl' \<in> Nl" and fst_Bl': "fst Bl' = B'"
      using in_N unfolding N_def by blast
    have "Bl' \<in> Bot_FL" unfolding Bot_FL_def using fst_Bl' in_Bot vimage_fst by fastforce
    then show \<open>\<exists>Bl'\<in>Bot_FL. Bl' \<in> Nl\<close> using in_Nl by blast
  qed
qed

end


end