theory DPLL_WNOT
  imports DPLL_W DPLL_NOT
begin


section \<open>Equivalence between both DPLL version\<close>

interpretation dpll\<^sub>N\<^sub>O\<^sub>T: dpll_with_backtrack .

declare dpll\<^sub>N\<^sub>O\<^sub>T.state_simp\<^sub>N\<^sub>O\<^sub>T[simp del]
lemma state_eq\<^sub>N\<^sub>O\<^sub>T_iff_eq[iff, simp]: "dpll\<^sub>N\<^sub>O\<^sub>T.state_eq\<^sub>N\<^sub>O\<^sub>T S T \<longleftrightarrow> S = T"
  unfolding dpll\<^sub>N\<^sub>O\<^sub>T.state_eq\<^sub>N\<^sub>O\<^sub>T_def by (cases S, cases T) auto

lemma dpll\<^sub>W_dpll\<^sub>W_bj:
  assumes inv: "dpll\<^sub>W_all_inv S" and dpll: "dpll\<^sub>W S T"
  shows "dpll\<^sub>N\<^sub>O\<^sub>T.dpll_bj S T "
  using dpll inv
  apply (induction rule: dpll\<^sub>W.induct)
    apply (rule dpll\<^sub>N\<^sub>O\<^sub>T.bj_propagate\<^sub>N\<^sub>O\<^sub>T)
    apply (rule dpll\<^sub>N\<^sub>O\<^sub>T.propagate\<^sub>N\<^sub>O\<^sub>T.propagate\<^sub>N\<^sub>O\<^sub>T; fastforce)
   apply (rule dpll\<^sub>N\<^sub>O\<^sub>T.bj_decide\<^sub>N\<^sub>O\<^sub>T)
   apply (rule dpll\<^sub>N\<^sub>O\<^sub>T.decide\<^sub>N\<^sub>O\<^sub>T.decide\<^sub>N\<^sub>O\<^sub>T; fastforce)
  apply (frule dpll\<^sub>N\<^sub>O\<^sub>T.backtrack.intros[of _ _ _ _ _], simp_all)
  apply (rule dpll\<^sub>N\<^sub>O\<^sub>T.dpll_bj.bj_backjump)
  apply (rule dpll\<^sub>N\<^sub>O\<^sub>T.backtrack_is_backjump'',
    simp_all add: dpll\<^sub>W_all_inv_def)
  done

lemma dpll\<^sub>W_bj_dpll:
  assumes inv: "dpll\<^sub>W_all_inv S" and dpll: "dpll\<^sub>N\<^sub>O\<^sub>T.dpll_bj S T"
  shows "dpll\<^sub>W S T"
  using dpll
  apply (induction rule: dpll\<^sub>N\<^sub>O\<^sub>T.dpll_bj.induct)
    apply (elim dpll\<^sub>N\<^sub>O\<^sub>T.decide\<^sub>N\<^sub>O\<^sub>TE, cases S)
    apply (frule decided; simp)
   apply (elim dpll\<^sub>N\<^sub>O\<^sub>T.propagate\<^sub>N\<^sub>O\<^sub>TE, cases S)
   apply (auto intro!: propagate[of _ _ "(_, _)", simplified])[]
  apply (elim dpll\<^sub>N\<^sub>O\<^sub>T.backjumpE, cases S)
  by (simp add: dpll\<^sub>W.simps dpll_with_backtrack.backtrack.simps)

lemma dpll\<^sub>W_dpll\<^sub>N\<^sub>O\<^sub>T: (* \htmllink{dpllW_dpllNOT} *)
  assumes inv: "dpll\<^sub>W_all_inv S"
  shows "dpll\<^sub>N\<^sub>O\<^sub>T.dpll_bj S T \<longleftrightarrow> dpll\<^sub>W S T"
  using assms dpll\<^sub>W_bj_dpll dpll\<^sub>W_dpll\<^sub>W_bj by blast

lemma rtranclp_dpll\<^sub>W_rtranclp_dpll\<^sub>N\<^sub>O\<^sub>T:
  assumes "dpll\<^sub>W\<^sup>*\<^sup>* S T " and "dpll\<^sub>W_all_inv S"
  shows "dpll\<^sub>N\<^sub>O\<^sub>T.dpll_bj\<^sup>*\<^sup>* S T"
  using assms apply induction
   apply (simp; fail)
  by (auto intro:  rtranclp_dpll\<^sub>W_all_inv dpll\<^sub>W_dpll\<^sub>W_bj rtranclp.rtrancl_into_rtrancl)

lemma rtranclp_dpll_rtranclp_dpll\<^sub>W:
  assumes "dpll\<^sub>N\<^sub>O\<^sub>T.dpll_bj\<^sup>*\<^sup>* S T " and "dpll\<^sub>W_all_inv S"
  shows "dpll\<^sub>W\<^sup>*\<^sup>* S T"
  using assms apply induction
   apply (simp; fail)
  by (auto intro: dpll\<^sub>W_bj_dpll rtranclp.rtrancl_into_rtrancl rtranclp_dpll\<^sub>W_all_inv)

lemma dpll_conclusive_state_correctness:
  assumes "dpll\<^sub>N\<^sub>O\<^sub>T.dpll_bj\<^sup>*\<^sup>* ([], N) (M, N)" and "conclusive_dpll\<^sub>W_state (M, N)"
  shows "M \<Turnstile>asm N \<longleftrightarrow> satisfiable (set_mset N)"
proof -
  have "dpll\<^sub>W_all_inv ([], N)"
    unfolding dpll\<^sub>W_all_inv_def by auto
  show ?thesis
    apply (rule dpll\<^sub>W_conclusive_state_correct)
     apply (simp add: \<open>dpll\<^sub>W_all_inv ([], N)\<close> assms(1) rtranclp_dpll_rtranclp_dpll\<^sub>W)
    using assms(2) by simp
qed

end
