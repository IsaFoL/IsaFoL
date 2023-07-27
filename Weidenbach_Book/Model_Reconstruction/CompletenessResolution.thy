(* Title: Proof of Resolution Completeness
    Author: Katharina Wagner
*)

theory CompletenessResolution
  imports Entailment_Definition.Partial_Herbrand_Interpretation
begin


lemma completeness_resolution:
  assumes "consistent_interp I" and
          "I \<Turnstile> C + D" and
       "L \<notin># C" and "-L \<notin># C" and "L \<notin># D" and "-L \<notin># D"
  obtains I' where "consistent_interp I'" and "I' \<Turnstile> add_mset L C" and " I' \<Turnstile> add_mset (-L) D"
proof (cases "I \<Turnstile> C")
  case True
  let ?I' = "(I - {L, -L}) \<union> {-L}"
  assume "I \<Turnstile> C"
  hence "consistent_interp ?I'" and "?I' \<Turnstile> C" and  "?I' \<Turnstile> add_mset L C" and "?I' \<Turnstile> add_mset (-L) D"
    using assms by (auto simp: true_cls_def intro: consistent_interp_subset)
  then show ?thesis by (meson that) 
next
  case False
  let ?I' = "(I - {L, -L}) \<union> {L}"
  assume "\<not>I \<Turnstile> C"
  hence "I \<Turnstile> D"
    using assms(2) by blast 
  hence "consistent_interp ?I'" and "?I' \<Turnstile> D" and "?I' \<Turnstile> add_mset (-L) D" and "?I' \<Turnstile> add_mset L C"
    using assms by (auto simp: true_cls_def intro: consistent_interp_subset)
  then show ?thesis by (meson that)
qed
end

