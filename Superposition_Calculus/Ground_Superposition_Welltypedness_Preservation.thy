theory Ground_Superposition_Welltypedness_Preservation
  imports Ground_Superposition Ground_Typing
begin

locale ground_superposition_welltypedness_preservation = 
  ground_superposition_calculus where select = select + 
  ground_typing where \<F> = \<F>
for 
  select :: "'f gatom clause \<Rightarrow> 'f gatom clause" and
  \<F> :: "('f, 'ty) fun_types"
begin

lemma ground_superposition_preserves_typing:
  assumes
    step: "superposition D E C" and
    wt_D: "clause.is_welltyped D" and
    wt_E: "clause.is_welltyped E"
  shows "clause.is_welltyped C"
  using assms
  by(cases rule: superposition.cases) (auto 4 3)

lemma ground_eq_resolution_preserves_typing:
  assumes
    step: "eq_resolution D C" and
    wt_D: "clause.is_welltyped D"
  shows "clause.is_welltyped C"
  using assms
  by(cases rule: eq_resolution.cases) auto

lemma ground_eq_factoring_preserves_typing:
  assumes
    step: "eq_factoring D C" and
    wt_D: "clause.is_welltyped D"
  shows "clause.is_welltyped C"
  using assms
  by(cases rule: eq_factoring.cases) auto

end

end
