theory Superposition_Welltypedness_Preservation
  imports Superposition
begin

context superposition_calculus
begin

lemma eq_resolution_preserves_typing:
  assumes "eq_resolution (D, \<V>) (C, \<V>)"  "clause.is_welltyped \<V> D"
  shows "clause.is_welltyped \<V> C"
  using assms
  by(cases "(D, \<V>)" "(C, \<V>)" rule: eq_resolution.cases) auto

lemma eq_factoring_preserves_typing:
  assumes "eq_factoring (D, \<V>) (C, \<V>)" "clause.is_welltyped \<V> D"
  shows "clause.is_welltyped \<V> C"
  using assms
  by (cases "(D, \<V>)" "(C, \<V>)" rule: eq_factoring.cases) fastforce

lemma superposition_preserves_typing:
  assumes
    superposition: "superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)" and
    D_is_welltyped: "clause.is_welltyped \<V>\<^sub>2 D" and
    E_is_welltyped: "clause.is_welltyped \<V>\<^sub>1 E"
  shows "clause.is_welltyped \<V>\<^sub>3 C"
  using superposition
proof (cases "(D, \<V>\<^sub>2)" "(E, \<V>\<^sub>1)" "(C, \<V>\<^sub>3)" rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 l\<^sub>1 E' l\<^sub>2 D' \<P> c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)

  then have welltyped_\<mu>: "is_welltyped \<V>\<^sub>3 \<mu>"
    by meson

  have "clause.is_welltyped \<V>\<^sub>3 (E \<cdot> \<rho>\<^sub>1)"
    using E_is_welltyped clause.is_welltyped.typed_renaming[OF superpositionI(1, 12)]
    by blast

  then have E\<mu>_is_welltyped: "clause.is_welltyped \<V>\<^sub>3 (E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
    using welltyped_\<mu>
    by simp
   
  have "clause.is_welltyped \<V>\<^sub>3 (D \<cdot> \<rho>\<^sub>2)"
    using D_is_welltyped clause.is_welltyped.typed_renaming[OF superpositionI(2, 13)] 
    by blast    

  then have D\<mu>_is_welltyped: "clause.is_welltyped \<V>\<^sub>3 (D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)"
    using welltyped_\<mu>
    by simp

  have imgu: "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> = t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>"
    using term.is_imgu_unifies'[OF superpositionI(10)].

  from literal_cases[OF superpositionI(6)] E\<mu>_is_welltyped D\<mu>_is_welltyped imgu
  show ?thesis
    unfolding superpositionI
    by cases auto
qed

end

end
