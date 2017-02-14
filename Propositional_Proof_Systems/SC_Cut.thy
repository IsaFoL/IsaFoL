theory SC_Cut
imports SC
begin
  
subsubsection\<open>Contraction\<close>
  
text\<open>First, we need contraction:\<close>
lemma contract:
  shows "(F,F,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta> \<down> n) \<and> (\<Gamma> \<Rightarrow> F,F,\<Delta> \<down> n \<longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta> \<down> n)"
proof(induction n arbitrary: F \<Gamma> \<Delta>)
  case (Suc n)
  hence IH: "F, F, \<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> F, \<Gamma> \<Rightarrow> \<Delta> \<down> n" "\<Gamma> \<Rightarrow> F, F, \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> F, \<Delta> \<down> n" for F \<Gamma> \<Delta> by blast+
  show ?case proof(intro conjI allI impI, goal_cases)
    case 1
    let ?ffs = "\<lambda>\<Gamma>. \<Gamma> - {# F #} - {# F #}"
    from 1 show ?case proof(insert 1; cases rule: SCc.cases[of "F,F,\<Gamma>" \<Delta> "Suc n"])
      case (NotL  \<Gamma>' G)
      show ?thesis
      proof(cases)
        assume e: "F = \<^bold>\<not>G"
        with NotL have \<Gamma>': "\<Gamma>' = \<^bold>\<not>G, \<Gamma>" by simp
        from NotL_inv NotL(2) have "\<Gamma> \<Rightarrow> G, G, \<Delta> \<down> n" unfolding \<Gamma>' .
        with IH(2) have "\<Gamma> \<Rightarrow> G, \<Delta> \<down> n" .
        with SCc.NotL show ?thesis unfolding e .
      next
        assume e: "F \<noteq> \<^bold>\<not>G"
        have ?thesis
          using NotL(2) IH(1)[of F "?ffs \<Gamma>'" "G, \<Delta>"] SCc.NotL[of "F, \<Gamma>' - {# F #} - {# F #}" G \<Delta> n]
          using e NotL(1) by (metis insert_DiffM lem1)
        from e NotL(1) have \<Gamma>: "\<Gamma> = \<^bold>\<not> G, ?ffs \<Gamma>'" by (meson lem1)
        with NotL(1) have \<Gamma>': "F,F,?ffs \<Gamma>' = \<Gamma>'" by simp
        show ?thesis using NotL(2) IH(1)[of F "?ffs \<Gamma>'" "G, \<Delta>"] SCc.NotL[of "F, ?ffs \<Gamma>'" G \<Delta> n] \<open>F, \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n\<close> by blast
      qed
    next
      case (AndL G H \<Gamma>') show ?thesis proof cases
        assume e: "F = And G H"
        with AndL(1) have \<Gamma>': "\<Gamma>' = And G H, \<Gamma>" by simp
        have "G \<^bold>\<and> H, G, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" using AndL(2) unfolding \<Gamma>' by auto
        hence "G, H, G, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" by(rule AndL_inv)
        hence "G, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" using IH(1) by (metis inL1 inL3)
        thus "F, \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n" using e SCc.AndL by simp
      next
        assume ne: "F \<noteq> And G H"
        with AndL(1) have \<Gamma>: "\<Gamma> = And G H, ?ffs \<Gamma>'" by (metis (no_types, lifting) diff_diff_add lem2)
        have "F, F, G, H, ?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" using AndL(2) using \<Gamma> inL4 local.AndL(1) by auto
        hence "G, H, F, ?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" using IH(1) inL2 by blast
        thus ?thesis using SCc.AndL unfolding \<Gamma> using inL1 by blast
      qed
    next
      case (OrL G \<Gamma>' H) show ?thesis proof cases
        assume e: "F = Or G H"
        with OrL(1) have \<Gamma>': "\<Gamma>' = Or G H, \<Gamma>" by simp
        have "Or G H, G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" "Or G H, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" using OrL(2,3) unfolding \<Gamma>' by simp_all
        hence "G, G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" "H, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" using OrL_inv by blast+
        hence "G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" "H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" using IH(1) by presburger+
        thus "F, \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n" unfolding e using SCc.OrL by simp
      next
        assume ne: "F \<noteq> Or G H"
        with OrL(1) have \<Gamma>: "\<Gamma> = Or G H, ?ffs \<Gamma>'" by (metis (no_types, lifting) diff_diff_add lem2)
        have "F, F, G, ?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" "F, F, H,?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" using OrL(2,3)
          by (metis add_mset_remove_trivial_If inL2 insert_noteq_member local.OrL(1) ne weakenL)+
        hence "G, F, ?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" "H, F, ?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" using IH(1) by(metis add_mset_commute)+
        thus ?thesis using SCc.OrL unfolding \<Gamma> by (metis add_mset_commute)
      qed
    next
      case (ImpL \<Gamma>' G H) show ?thesis proof cases
        assume e: "F = Imp G H"
        with ImpL(1) have \<Gamma>': "\<Gamma>' = Imp G H, \<Gamma>" by simp
        have "H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" "\<Gamma> \<Rightarrow> G,\<Delta> \<down> n" using IH ImpL_inv ImpL(2,3) unfolding \<Gamma>' 
          by (metis add_mset_commute)+
        thus ?thesis unfolding e using SCc.ImpL by simp
      next
        assume ne: "F \<noteq> Imp G H"
        with ImpL(1) have \<Gamma>: "\<Gamma> = Imp G H, ?ffs \<Gamma>'" by (metis (no_types, lifting) diff_diff_add lem2)
        have "F, F, ?ffs \<Gamma>' \<Rightarrow> G, \<Delta> \<down> n" "F, F, H, ?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" using ImpL(2,3)
          by (metis add_mset_remove_trivial_If inL2 insert_noteq_member ImpL ne weakenL)+
        thus ?thesis using SCc.ImpL IH unfolding \<Gamma> by (metis add_mset_commute)
      qed
    next
      case ImpR thus ?thesis by (simp add: IH(1) SCc.intros(10) add_mset_commute)
    next
      case (NotR G \<Delta>') thus ?thesis using IH(1) by (simp add: SCc.NotR add_mset_commute)
    qed (auto intro: IH SCc.intros(1,2) intro!: SCc.intros(3-10))
  next
    case 2
    let ?ffs = "\<lambda>\<Gamma>. \<Gamma> - {# F #} - {# F #}"
    have not_principal[dest]:
      "\<lbrakk>F \<noteq> f G H; F, F, \<Delta> = f G H, \<Delta>'\<rbrakk> \<Longrightarrow> \<Delta> = f G H, ?ffs \<Delta>' \<and> F, F, ?ffs \<Delta>' = \<Delta>'" for f G H \<Delta>' proof(intro conjI, goal_cases)
        case 2
        from 2 have "F \<in># \<Delta>'" by(blast dest: lem1[THEN iffD1])
        then obtain \<Delta>'' where \<Delta>': "\<Delta>' = F,\<Delta>''"  by (metis insert_DiffM)
        with 2(2) have "F, \<Delta> = f G H, \<Delta>''" by(simp add: add_mset_commute)
        hence "F \<in># \<Delta>''" using 2(1) by(blast dest: lem1[THEN iffD1])
        then obtain \<Delta>''' where \<Delta>'': "\<Delta>'' = F,\<Delta>'''" by (metis insert_DiffM)
        show ?case unfolding \<Delta>' \<Delta>'' by simp
        case 1 show ?case using 1(2) unfolding \<Delta>' \<Delta>'' by(simp add: add_mset_commute)
      qed
    have principal[dest]: "F, F, \<Delta> = f G H, \<Delta>' \<Longrightarrow> F = f G H \<Longrightarrow> \<Delta>' = f G H, \<Delta>" for f G H \<Delta>' by simp
    from 2 show ?case proof(cases rule: SCc.cases[of \<Gamma> "F,F,\<Delta>" "Suc n"])
      case (ImpR G H \<Delta>') thus ?thesis proof cases
        assume e[simp]: "F = Imp G H"
        with ImpR(1) have \<Delta>'[simp]: "\<Delta>' = Imp G H, \<Delta>" by simp
        have "G, \<Gamma> \<Rightarrow> Imp G H, H, \<Delta> \<down> n" using ImpR(2) by simp
        hence "G, G, \<Gamma> \<Rightarrow> H, H, \<Delta> \<down> n" by(rule ImpR_inv)
        hence "G, \<Gamma> \<Rightarrow> H, \<Delta> \<down> n" using IH by fast
        thus "\<Gamma> \<Rightarrow> F, \<Delta> \<down> Suc n" using SCc.ImpR by simp
      next
        assume a: "F \<noteq> Imp G H"
        with ImpR(1) have \<Delta>: "\<Delta> = Imp G H, ?ffs \<Delta>'" by (metis (no_types, lifting) diff_diff_add lem2)
        have "G,\<Gamma> \<Rightarrow> F, F, H, ?ffs \<Delta>' \<down> n" using ImpR(2)
            by (metis a add_mset_remove_trivial_If inR2 insert_noteq_member local.ImpR(1) weakenR)
        thus ?thesis using SCc.ImpR IH unfolding \<Delta> by (metis add_mset_commute)
      qed
    next
      case (AndR G \<Delta>' H) thus ?thesis proof(cases "F = And G H")
        case True thus ?thesis using AndR_inv IH(2) AndR SCc.AndR by (metis add_mset_commute add_mset_remove_trivial) (* yeah, sledgehammer is actually smart enough, we could have saved us the verbosity from above *)
      next
        case False 
        hence e: "\<Delta> = And G H, ?ffs \<Delta>'" using AndR(1) using diff_diff_add lem2 by blast
        hence "G \<^bold>\<and> H, F, F, ?ffs \<Delta>' = G \<^bold>\<and> H, \<Delta>'" using AndR(1) by simp
        hence "\<Gamma> \<Rightarrow> F, F, G, ?ffs \<Delta>' \<down> n" "\<Gamma> \<Rightarrow> F, F, H, ?ffs \<Delta>' \<down> n" using AndR(2,3) using add_left_imp_eq inR2 by auto
        hence "\<Gamma> \<Rightarrow> G, F, ?ffs \<Delta>' \<down> n" "\<Gamma> \<Rightarrow> H, F, ?ffs \<Delta>' \<down> n" using IH(2) by fast+
        thus ?thesis unfolding e by(intro SCc.AndR[THEN inR1])
      qed
    next
    case (OrR G H \<Delta>') thus ?thesis proof cases
      assume a: "F = Or G H" 
      hence \<Delta>': "\<Delta>' = G \<^bold>\<or> H, \<Delta>" using OrR(1) by(intro principal)
      hence "\<Gamma> \<Rightarrow> G, H, G, H, \<Delta> \<down> n" using inR3[THEN OrR_inv] OrR(2) by auto
      hence "\<Gamma> \<Rightarrow> H, G, \<Delta> \<down> n" using IH(2)[of \<Gamma> G "H,H,\<Delta>"] IH(2)[of \<Gamma> H "G,\<Delta>"]
        unfolding add_ac(3)[of "{#H#}" "{#G#}"] using inR2  by blast
      hence "\<Gamma> \<Rightarrow> G, H, \<Delta> \<down> n" by(elim SC_swap_applies)
    thus ?thesis unfolding a by (simp add: SCc.OrR)
    next
      assume a: "F \<noteq> Or G H"
      with not_principal have np: "\<Delta> = G \<^bold>\<or> H, ?ffs \<Delta>' \<and> F, F, ?ffs \<Delta>' = \<Delta>'" using OrR(1) .
      with OrR(2) have "\<Gamma> \<Rightarrow> G, H, F, ?ffs \<Delta>' \<down> n" using IH(2) by (metis inR2 inR4)
      hence "\<Gamma> \<Rightarrow> F, G \<^bold>\<or> H, ?ffs \<Delta>' \<down> Suc n" by(intro SCc.OrR[THEN inR1])
      thus ?thesis using np by simp
    qed
    next
      case (NotR G \<Delta>') thus ?thesis proof(cases "F = Not G") 
        case True 
        with principal NotR(1) have "\<Delta>' = \<^bold>\<not> G, \<Delta>" .
        with NotR_inv NotR(2) have "G, G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" by blast
        with IH(1) have "G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" .
        thus "\<Gamma> \<Rightarrow> F, \<Delta> \<down> Suc n" unfolding True by(intro SCc.NotR)
      next
        case False 
        with not_principal have np: "\<Delta> = \<^bold>\<not> G, \<Delta>' - (F, {#F#}) \<and> F, F, \<Delta>' - (F, {#F#}) = \<Delta>'" using NotR(1) by auto
        hence "G, \<Gamma> \<Rightarrow> F, F, ?ffs \<Delta>' \<down> n" using NotR(2) by simp
        hence "G, \<Gamma> \<Rightarrow> F, ?ffs \<Delta>' \<down> n" by(elim IH(2))
        thus ?thesis using np SCc.NotR inR1 by auto
      qed
    next
      case BotL thus ?thesis by(elim SCc.BotL)
    next
      case (Ax k) thus ?thesis by(intro SCc.Ax[where k=k]) simp_all
    next
      case NotL thus ?thesis by (simp add: SCc.NotL Suc.IH add_mset_commute)
    next
      case AndL thus ?thesis using SCc.AndL Suc.IH by blast
    next
      case OrL thus ?thesis using SCc.OrL Suc.IH by presburger
    next
      case ImpL thus ?thesis by (metis SCc.ImpL Suc.IH add_mset_commute)
    qed
  qed
qed blast
corollary
  shows contractL: "F,F,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta> \<down> n"
  and contractR: "\<Gamma> \<Rightarrow> F,F,\<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta> \<down> n"
  and contractL': "F,F,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta>"
  and contractR': "\<Gamma> \<Rightarrow> F,F,\<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta>"
  unfolding SC_SCp_eq[symmetric] using contract by blast+
    
subsubsection\<open>Cut\<close>
  
text\<open>Which cut rule we show is up to us:\<close>
lemma cut_cs_cf:
  assumes context_sharing_Cut: "\<And>A \<Gamma> \<Delta>. \<Gamma> \<Rightarrow> A,\<Delta> \<Longrightarrow> A,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
  shows context_free_Cut: "\<Gamma> \<Rightarrow> A,\<Delta> \<Longrightarrow> A,\<Gamma>' \<Rightarrow> \<Delta>' \<Longrightarrow> \<Gamma> + \<Gamma>' \<Rightarrow> \<Delta> + \<Delta>'"
  by(intro context_sharing_Cut[of "\<Gamma> + \<Gamma>'" A "\<Delta> + \<Delta>'"])
    (metis add.commute union_mset_add_mset_left weakenL_set' weakenR_set')+
lemma cut_cf_cs:
  assumes context_free_Cut: "\<And>A \<Gamma> \<Gamma>' \<Delta> \<Delta>'. \<Gamma> \<Rightarrow> A,\<Delta> \<Longrightarrow> A,\<Gamma>' \<Rightarrow> \<Delta>' \<Longrightarrow> \<Gamma> + \<Gamma>' \<Rightarrow> \<Delta> + \<Delta>'"
  shows context_sharing_Cut: "\<Gamma> \<Rightarrow> A,\<Delta> \<Longrightarrow> A,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
proof - 
  have contract\<Gamma>\<Gamma>: "\<Gamma>+\<Gamma>' \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma>' \<subseteq># \<Gamma> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>" for \<Gamma> \<Gamma>' \<Delta>
  proof(induction "\<Gamma>'" arbitrary: \<Gamma>)
    case empty thus ?case using weakenL_set by force
  next
    case (add x \<Gamma>' \<Gamma>)
    from add.prems(2) have "x \<in># \<Gamma>" by (simp add: insert_subset_eq_iff)
    then obtain \<Gamma>'' where \<Gamma>[simp]: "\<Gamma> = x,\<Gamma>''" by (meson multi_member_split)
    from add.prems(1) have "x,x,\<Gamma>'' + \<Gamma>' \<Rightarrow> \<Delta>" by simp
    with contractL' have "x, \<Gamma>'' + \<Gamma>' \<Rightarrow> \<Delta>" .
    with add.IH[of \<Gamma>] show ?case using \<Gamma>  add.prems(2) subset_mset.order.trans by force
  qed
  have contract\<Delta>\<Delta>: "\<Gamma> \<Rightarrow> \<Delta>+\<Delta>' \<Longrightarrow> \<Delta>' \<subseteq># \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>" for \<Gamma> \<Delta> \<Delta>'
  proof(induction "\<Delta>'" arbitrary: \<Delta>)
    case empty thus ?case using weakenL_set by force
  next
    case (add x \<Delta>' \<Delta>)
    from add.prems(2) have "x \<in># \<Delta>" by (simp add: insert_subset_eq_iff)
    then obtain \<Delta>'' where \<Delta>[simp]: "\<Delta> = x,\<Delta>''" by (metis multi_member_split)
    from add.prems(1) have "\<Gamma> \<Rightarrow> x,x,\<Delta>'' + \<Delta>'" by simp
    with contractR' have "\<Gamma> \<Rightarrow> x, \<Delta>'' + \<Delta>'" .
    with add.IH[of \<Delta>] show ?case using \<Delta> add.prems(2) subset_mset.order.trans by force
  qed
  show "\<Gamma> \<Rightarrow> A,\<Delta> \<Longrightarrow> A,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
    using context_free_Cut[of \<Gamma> A \<Delta> \<Gamma> \<Delta>] contract\<Gamma>\<Gamma> contract\<Delta>\<Delta>
    by blast
qed
(* since these are the only lemmas that need contraction on sets, I've decided to transfer those in place *)
text\<open>According to Troelstra and Schwichtenberg~\cite{troelstra2000basic}, the sharing variant is the one we want to prove.\<close>
  
lemma Cut_Atom_pre: "Atom k,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> Atom k,\<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
proof(induction "Atom k,\<Gamma>" "\<Delta>" arbitrary: \<Gamma> rule: SCp.induct)
  case (BotL \<Delta>)
  hence "\<bottom> \<in># \<Gamma>" by simp
  thus ?case using SCp.BotL by blast
next
  case (Ax l \<Delta>)
  show ?case proof cases
    assume "l = k"
    with \<open>Atom l \<in># \<Delta>\<close> obtain \<Delta>' where "\<Delta> = Atom k, \<Delta>'" by (meson multi_member_split)
    with \<open>\<Gamma> \<Rightarrow> Atom k, \<Delta>\<close> have "\<Gamma> \<Rightarrow> \<Delta>" using contractR' by blast
    thus ?thesis by auto
  next
    assume "l \<noteq> k"
    with \<open>Atom l \<in># Atom k, \<Gamma>\<close> have "Atom l \<in># \<Gamma>" by simp
    with \<open>Atom l \<in># \<Delta>\<close> show ?thesis using SCp.Ax by blast
  qed
next
  case (NotL \<Gamma>' F \<Delta>)
  obtain \<Gamma>'' where \<Gamma>: "\<Gamma> = Not F, \<Gamma>''" by (meson NotL.hyps(3) add_eq_conv_ex form.simps(9))
  show ?case unfolding \<Gamma>
    apply(intro SCp.NotL)
    apply(intro NotL.hyps (* IH *))
     subgoal using NotL \<Gamma> by (simp add: lem2)
    subgoal using \<Gamma> NotL.prems NotL_inv' by blast
  done
next
  case (NotR F \<Delta>)
  then show ?case by(auto intro!: SCp.NotR dest!: NotR_inv')
next
  case (AndL F G \<Gamma>' \<Delta>)
  obtain \<Gamma>'' where \<Gamma>: "\<Gamma> = And F G, \<Gamma>''" by (meson AndL.hyps(3) add_eq_conv_ex form.simps)
  show ?case unfolding \<Gamma>
    apply(intro SCp.AndL)
    apply(intro AndL.hyps (* IH *))
    subgoal using AndL \<Gamma> by (simp add: lem2)
    subgoal using \<Gamma> AndL.prems AndL_inv' by blast
  done
next
  case (AndR F \<Delta> G)
  then show ?case
    using AndR_inv' SCp.AndR by blast
next
  case (OrL F \<Gamma>' \<Delta> G)
  obtain \<Gamma>'' where \<Gamma>: "\<Gamma> = Or F G, \<Gamma>''" by (meson OrL.hyps(5) add_eq_conv_ex form.simps(13))
  have ihm: "F, \<Gamma>' = Atom k, F, \<Gamma>''" "G, \<Gamma>' = Atom k, G, \<Gamma>''" using OrL \<Gamma> by (simp_all add: lem2)
  show ?case unfolding \<Gamma>
    apply(intro SCp.OrL OrL.hyps(2)[OF ihm(1)] OrL.hyps(4)[OF ihm(2)])
     subgoal using \<Gamma> OrL.prems OrL_inv' by blast
    subgoal using \<Gamma> OrL.prems OrL_inv' by blast
  done
next
  case (OrR F G \<Delta>)
  then show ?case by (metis NotL_inv' OrR_inv' SCp.NotL SCp.OrR) (* curious\<dots> *)
next
  case (ImpL \<Gamma>' F \<Delta> G)
  obtain \<Gamma>'' where \<Gamma>: "\<Gamma> = Imp F G, \<Gamma>''" by (meson ImpL.hyps(5) add_eq_conv_ex form.simps)
  show ?case unfolding \<Gamma>
    apply(intro SCp.ImpL ImpL.hyps(2) ImpL.hyps(4))
    subgoal using ImpL \<Gamma> by (simp add: lem2)
    subgoal using \<Gamma> ImpL.prems ImpL_inv' by blast
    subgoal using ImpL \<Gamma> by (simp add: lem2)
    subgoal using \<Gamma> ImpL.prems ImpL_inv' by blast
  done
next
  case (ImpR F G \<Delta>)
  then show ?case by (auto dest!: ImpR_inv' intro!: SCp.ImpR)
qed
  
text\<open>We can show the admissibility of the cut rule by induction on the cut formula 
(or, if you will, as a procedure that splits the cut into smaller formulas that get cut).
The only mildly complicated case is that of cutting in an @{term "Atom k"}.
It is, contrary to the general case, only mildly complicated, since the cut formula can only appear principal in the axiom rules.\<close>

theorem cut': "\<Gamma> \<Rightarrow> A,\<Delta> \<Longrightarrow> A,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
proof(induction A arbitrary: \<Gamma> \<Delta>)
  case (Atom k) thus ?case using Cut_Atom_pre by meson
next
  case Bot thus ?case using Cut_Bot_pre' by fastforce 
next
  case (Not A)
  with  NotL_inv' NotR_inv' show ?case by blast
next
  case (And F G) thus ?case using SC_SCp_eq by (meson AndL_inv AndR_inv weakenL)
next
  case (Or F G) thus ?case using SC_SCp_eq by (meson OrL_inv OrR_inv weakenR)
next
  case (Imp F G)
  from ImpR_inv' \<open>\<Gamma> \<Rightarrow> F \<^bold>\<rightarrow> G, \<Delta>\<close> have R: "F, \<Gamma> \<Rightarrow> G, \<Delta>" by blast
  from ImpL_inv' \<open>F \<^bold>\<rightarrow> G, \<Gamma> \<Rightarrow> \<Delta>\<close> have L: "\<Gamma> \<Rightarrow> F, \<Delta>" "G, \<Gamma> \<Rightarrow> \<Delta>" by blast+
  from L(1) have "\<Gamma> \<Rightarrow> F, G, \<Delta>" using weakenR' add_ac(3) by blast
  with R have "\<Gamma> \<Rightarrow> G, \<Delta>" using Imp.IH(1) by simp
  with L(2) show "\<Gamma> \<Rightarrow> \<Delta>" using Imp.IH(2) by clarsimp
qed
  (* For this proof to work with FOL, I think we would need very special inversion rules.
  For example, for \<forall>R, we would need that there's a (finite!) multiset of substitutions S, such that
  instead of having \<forall>x.F,\<Delta>, having {F[s/x] | s \<in> S} + \<Delta> is enough. I don't think that holds\<dots> *)
  
corollary cut_cf: "\<lbrakk> \<Gamma> \<Rightarrow> A, \<Delta>; A, \<Gamma>' \<Rightarrow> \<Delta>'\<rbrakk> \<Longrightarrow> \<Gamma> + \<Gamma>' \<Rightarrow> \<Delta> + \<Delta>'"
  using cut_cs_cf cut' SC_SCp_eq by metis

lemma assumes cut: "\<And> \<Gamma>' \<Delta>' A. \<lbrakk>\<Gamma>' \<Rightarrow> A, \<Delta>'; A, \<Gamma>' \<Rightarrow> \<Delta>'\<rbrakk> \<Longrightarrow> \<Gamma>' \<Rightarrow> \<Delta>'"
  shows contraction_admissibility: "F,F,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta>"
  by(rule cut[of "F,\<Gamma>" F \<Delta>, OF extended_Ax]) simp_all
(* yes, chapman p 2/5, second to last paragraph. that's right. we can prove contraction with cut. but what's that good for? *)


end