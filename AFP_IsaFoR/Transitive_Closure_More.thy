theory Transitive_Closure_More imports Main begin

lemma (in order) rtranclp_less_eq [simp]:
  "(op \<le>)\<^sup>*\<^sup>* = op \<le>"
  by (intro ext) (auto elim: rtranclp_induct)

lemma (in order) tranclp_less [simp]:
  "(op <)\<^sup>+\<^sup>+ = op <"
  by (intro ext) (auto elim: tranclp_induct)

lemma (in order) rtranclp_greater_eq [simp]:
  "(op \<ge>)\<^sup>*\<^sup>* = op \<ge>"
  by (intro ext) (auto elim: rtranclp_induct)

lemma (in order) tranclp_greater [simp]:
  "(op >)\<^sup>+\<^sup>+ = op >"
  by (intro ext) (auto elim: tranclp_induct)

end