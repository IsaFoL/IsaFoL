subsubsection\<open>Alternate proofs for Cut and Contraction\<close>
theory MiniSC_Cut
imports MiniSC
begin
  
text\<open>We want to keep our original proofs of contraction and cut around, but these are sleeker.\<close>
lemma mini_contract:
  shows "is_mini_mset \<Gamma> \<Longrightarrow> is_mini_mset \<Delta> \<Longrightarrow> is_mini_formula F \<Longrightarrow>
  (F,F,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta> \<down> n) \<and> (\<Gamma> \<Rightarrow> F,F,\<Delta> \<down> n \<longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta> \<down> n)"
proof(induction n arbitrary: F \<Gamma> \<Delta>)
  case (Suc n)
  note pr = Suc.prems(1,2)[THEN bspec] Suc.prems(3)
  from Suc have IH1: "F, \<Gamma> \<Rightarrow> \<Delta> \<down> n" if "F, F, \<Gamma> \<Rightarrow> \<Delta> \<down> n"
    "is_mini_mset \<Gamma>" "is_mini_mset \<Delta>" "is_mini_formula F" for F \<Gamma> \<Delta> using that by blast
  from Suc have IH2: "\<Gamma> \<Rightarrow> F, \<Delta> \<down> n" if "\<Gamma> \<Rightarrow> F, F, \<Delta> \<down> n"
    "is_mini_mset \<Gamma>" "is_mini_mset \<Delta>" "is_mini_formula F" for F \<Gamma> \<Delta> using that by blast
  have GM: "F,F,\<Gamma> = G,\<Gamma>' \<Longrightarrow> is_mini_formula G" "\<Gamma> = G,\<Gamma>' \<Longrightarrow> is_mini_formula G" for G \<Gamma>'
    using pr insert_noteq_member by fastforce+
  have DM: "F,F,\<Delta> = G,\<Gamma>' \<Longrightarrow> is_mini_formula G" "\<Delta> = G,\<Gamma>' \<Longrightarrow> is_mini_formula G" for G \<Gamma>'
    using pr insert_noteq_member by fastforce+
  show ?case proof(intro conjI allI impI, goal_cases)
    case 1
    let ?ffs = "\<lambda>\<Gamma>. \<Gamma> - {# F #} - {# F #}"
    from 1 show ?case proof(insert 1; cases rule: SCc.cases[of "F,F,\<Gamma>" \<Delta> "Suc n"])
      case (NotL  \<Gamma>' G) hence False using Suc.prems insert_noteq_member by fastforce
      thus ?thesis ..
    next
      case (ImpL \<Gamma>' G H) show ?thesis proof cases
        assume e: "F = Imp G H"
        with ImpL(1) have \<Gamma>': "\<Gamma>' = Imp G H, \<Gamma>" by simp
        have "H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" "\<Gamma> \<Rightarrow> G,\<Delta> \<down> n" using IH1 IH2 ImpL_inv ImpL(2,3) unfolding \<Gamma>'
          by (metis Suc.prems e inL1 is_mini_formula.simps(3))+
        thus ?thesis unfolding e using SCc.ImpL by simp
      next
        assume ne: "F \<noteq> Imp G H"
        with ImpL(1) have \<Gamma>: "\<Gamma> = Imp G H, ?ffs \<Gamma>'" by (metis (no_types, lifting) diff_diff_add lem2)
        have "F, F, ?ffs \<Gamma>' \<Rightarrow> G, \<Delta> \<down> n" "F, F, H, ?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" using ImpL(2,3)
          by (metis add_mset_remove_trivial_If inL2 insert_noteq_member ImpL ne weakenL)+
        hence "F, H, ?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" "F, ?ffs \<Gamma>' \<Rightarrow> G, \<Delta> \<down> n"
          by (metis GM(1) IH1 Suc.prems(1,2) insert_iff \<Gamma> is_mini_formula.simps(3) set_mset_add_mset_insert)+
        thus ?thesis using SCc.ImpL unfolding \<Gamma>
          using inL1 by blast
      qed
    next
      case ImpR thus ?thesis 
        by (fastforce intro!: SCc.intros(10) dest: DM elim!: IH1 simp add: pr add_mset_commute)
    next
      case BotL thus ?thesis by (simp add: SCc.BotL)
    next
      case Ax thus ?thesis by (simp add: SCc.Ax)
    qed (metis GM(1) DM(2) is_mini_formula.simps)+
  next
    case 2
    let ?ffs = "\<lambda>\<Gamma>. \<Gamma> - {# F #} - {# F #}"
    from 2 show ?case proof(cases rule: SCc.cases[of \<Gamma> "F,F,\<Delta>" "Suc n"])
      case (ImpR G H \<Delta>') 
      have mf: "is_mini_formula G" "is_mini_formula H"
        using DM(1) is_mini_formula.simps(3) local.ImpR(1) by blast+
      show ?thesis proof cases        
        assume e[simp]: "F = Imp G H"
        with ImpR(1) have \<Delta>'[simp]: "\<Delta>' = Imp G H, \<Delta>" by simp
        have "G, \<Gamma> \<Rightarrow> Imp G H, H, \<Delta> \<down> n" using ImpR(2) by simp
        hence "G, G, \<Gamma> \<Rightarrow> H, H, \<Delta> \<down> n" by(rule ImpR_inv)
        hence "G, \<Gamma> \<Rightarrow> H, \<Delta> \<down> n" using IH1 IH2 
          by (metis e insertE is_mini_formula.simps(3) pr set_mset_add_mset_insert)
        thus "\<Gamma> \<Rightarrow> F, \<Delta> \<down> Suc n" using SCc.ImpR by simp
      next
        assume a: "F \<noteq> Imp G H"
        with ImpR(1) have \<Delta>: "\<Delta> = Imp G H, ?ffs \<Delta>'" by (metis (no_types, lifting) diff_diff_add lem2)
        have "G,\<Gamma> \<Rightarrow> F, F, H, ?ffs \<Delta>' \<down> n" using ImpR(2)
          by (metis a add_mset_remove_trivial_If inR2 insert_noteq_member local.ImpR(1) weakenR)
        thus ?thesis by(auto simp add: \<Delta> pr mf dest!: IH2 intro!: SCc.ImpR)
      qed
    next
      case BotL thus ?thesis by(elim SCc.BotL)
    next
      case (Ax k) thus ?thesis by(intro SCc.Ax[where k=k]) simp_all
    next
      case ImpL thus ?thesis by (fastforce
        intro!: SCc.intros(3-) dest: DM GM elim!: IH2 simp add: pr add_mset_commute)
    qed (metis GM(2) DM(1) is_mini_formula.simps)+
  qed
qed blast
corollary
  assumes "is_mini_formula F" "is_mini_mset \<Gamma>" "is_mini_mset \<Delta>"
  shows mini_contractL: "F,F,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta> \<down> n"
  and mini_contractR: "\<Gamma> \<Rightarrow> F,F,\<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta> \<down> n"
  and mini_contractL': "F,F,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta>"
  and mini_contractR': "\<Gamma> \<Rightarrow> F,F,\<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta>"
  unfolding SC_SCp_eq[symmetric] using mini_contract assms by blast+

lemma mini_Cut_Atom_pre: "Atom k,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> Atom k,\<Delta> \<Longrightarrow> 
  is_mini_mset \<Gamma> \<Longrightarrow> is_mini_mset \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
proof(induction "Atom k,\<Gamma>" "\<Delta>" arbitrary: \<Gamma> rule: SCp.induct)
  case (BotL \<Delta>)
  hence "\<bottom> \<in># \<Gamma>" by simp
  thus ?case using SCp.BotL by blast
next
  case (Ax l \<Delta>)
  show ?case proof cases
    assume "l = k"
    with \<open>Atom l \<in># \<Delta>\<close> obtain \<Delta>' where "\<Delta> = Atom k, \<Delta>'" by (meson multi_member_split)
    with \<open>\<Gamma> \<Rightarrow> Atom k, \<Delta>\<close> have "\<Gamma> \<Rightarrow> \<Delta>" using mini_contractR'
      by (metis Ax.prems(2) Ax.prems(3) insert_iff set_mset_add_mset_insert)
    thus ?thesis by auto
  next
    assume "l \<noteq> k"
    with \<open>Atom l \<in># Atom k, \<Gamma>\<close> have "Atom l \<in># \<Gamma>" by simp
    with \<open>Atom l \<in># \<Delta>\<close> show ?thesis using SCp.Ax by blast
  qed
next
  case (ImpL \<Gamma>' F \<Delta> G)
  obtain \<Gamma>'' where \<Gamma>: "\<Gamma> = Imp F G, \<Gamma>''" by (meson ImpL.hyps(5) add_eq_conv_ex form.simps)
  have *: "\<Gamma>'' \<Rightarrow> Atom k, F, \<Delta>" "G, \<Gamma>'' \<Rightarrow> Atom k, \<Delta>"  using \<Gamma> ImpL.prems ImpL_inv' by blast+
  show ?case unfolding \<Gamma> using ImpL \<Gamma> * by(auto intro!: SCp.ImpL ImpL.hyps(2) ImpL.hyps(4))
next
  case (ImpR F G \<Delta>)
  then show ?case by (auto dest!: ImpR_inv' intro!: SCp.ImpR)
qed (metis 
    form.distinct(3,5,7)
    is_mini_formula.simps(4,5,6) 
    insert_noteq_member set_mset_add_mset_insert insertI1)+

theorem mini_cut': "is_mini_formula A \<Longrightarrow> is_mini_mset \<Gamma> \<Longrightarrow> is_mini_mset \<Delta>
   \<Longrightarrow> \<Gamma> \<Rightarrow> A,\<Delta> \<Longrightarrow> A,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
proof(induction A arbitrary: \<Gamma> \<Delta>)
  case (Atom k) thus ?case using mini_Cut_Atom_pre by meson
next
  case Bot thus ?case using Cut_Bot_pre' by fastforce 
next
  case (Imp F G)
  from ImpR_inv' \<open>\<Gamma> \<Rightarrow> F \<^bold>\<rightarrow> G, \<Delta>\<close> have R: "F, \<Gamma> \<Rightarrow> G, \<Delta>" by blast
  from ImpL_inv' \<open>F \<^bold>\<rightarrow> G, \<Gamma> \<Rightarrow> \<Delta>\<close> have L: "\<Gamma> \<Rightarrow> F, \<Delta>" "G, \<Gamma> \<Rightarrow> \<Delta>" by blast+
  from L(1) have "\<Gamma> \<Rightarrow> F, G, \<Delta>" using weakenR' add_ac(3) by blast
  with R have "\<Gamma> \<Rightarrow> G, \<Delta>" using Imp.IH(1)
    by (metis Imp.prems(1-3) insertE is_mini_formula.simps(3) set_mset_add_mset_insert)
  with L(2) show "\<Gamma> \<Rightarrow> \<Delta>" using Imp.IH(2)
    using Imp.prems(1-3) is_mini_formula.simps by blast
qed auto

corollary "\<Gamma> \<Rightarrow> A,\<Delta> \<Longrightarrow> A,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
  using mini_cut'[OF to_mini_is_mini to_mini_mset_is to_mini_mset_is, of \<Gamma> A \<Delta>]
  unfolding image_mset_add_mset[symmetric] MiniSC_eq .
  

end