theory SC_Compl_Consistent
imports Consistency SC_Cut SC_Sema 
begin
(* TODO we only need contraction, and we only need \<Turnstile>\<Rightarrow>. meh. and we could also separate this into two theories. But I don't think that's worth it. *)
(* TODO: It's possible to do this without contraction, but let's just say that the proof gets slightly less sledgehammerous\<dots> *)

context begin
private lemma reasonable: 
  "\<forall>\<Gamma>'. F    \<cdot> set_mset \<Gamma> = set_mset \<Gamma>' \<longrightarrow> P \<Gamma>' \<Longrightarrow> P (F, \<Gamma>)" 
  "\<forall>\<Gamma>'. F \<cdot> G \<cdot> set_mset \<Gamma> = set_mset \<Gamma>' \<longrightarrow> P \<Gamma>' \<Longrightarrow> P (F, G, \<Gamma>)" by simp_all

lemma SC_consistent:  "pcp {set_mset \<Gamma>| \<Gamma>. \<not>(\<Gamma> \<Rightarrow> {#})}"
  unfolding pcp_def
  apply(intro ballI conjI; erule contrapos_pp; clarsimp; ((drule reasonable)+)?)
          apply(auto dest!: NotL_inv' AndL_inv' OrL_inv' ImpL_inv' NotR_inv' AndR_inv' OrR_inv' ImpR_inv' multi_member_split contractL' contractR' intro!: SCp.intros(3-))
    apply(auto simp: add_mset_commute intro: contractR' contractL' )
  apply (metis Ax_canonical add_eq_conv_diff form.distinct(3))
(* Alternatively, sledgehammer also finds slick proofs for the individual subgoals after the initial apply of the "reasonable"  lemmas
  subgoal by (simp add: SCp.BotL)
  subgoal by (metis Ax_canonical SCp.NotL contractL' mset_add)
  subgoal by (metis SCp.AndL contractL' insert_DiffM)
  subgoal by (metis SCp.OrL contractL' insert_DiffM)
  subgoal by (metis NotL_inv' SCp.ImpL contractL' insert_DiffM)
  subgoal by (metis SCp.NotL SCp.NotR contractL' insert_DiffM)
  subgoal by (metis NotL_inv' SCp.AndR SCp.NotL contractL' insert_DiffM)
  subgoal by (metis NotL_inv' SCp.NotL SCp.OrR contractL' inR1' insert_DiffM)
  subgoal by (metis NotL_inv' SCp.ImpR SCp.NotL contractL' inL1' insert_DiffM) *)
done
    
end

lemma "\<Turnstile> \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
proof(erule contrapos_pp)
  have NotInv: "\<Gamma> + image_mset Not \<Delta> \<Rightarrow> {#} \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
    by (induction \<Delta> arbitrary: \<Gamma>; simp add: NotL_inv')
  assume \<open>\<not> \<Gamma> \<Rightarrow> \<Delta>\<close>
  hence \<open>\<not> \<Gamma> + image_mset Not \<Delta> \<Rightarrow> {#}\<close> using NotInv by blast
  with pcp_sat[OF SC_consistent]
  have "sat (set_mset (\<Gamma> + image_mset \<^bold>\<not> \<Delta>))" by blast
  thus \<open>\<not> (\<Turnstile> \<Gamma> \<Rightarrow> \<Delta>)\<close> unfolding sat_def sequent_semantics_def not_all by (force elim!: ex_forward)
qed


end
