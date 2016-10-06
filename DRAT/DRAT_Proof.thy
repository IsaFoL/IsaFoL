theory DRAT_Proof
imports Unit_Propagation DRAT_Misc
begin
  section \<open>Miscellaneous\<close>

  text \<open>Ad-hoc tactic to solve locale subgoals that are similar to existing locale assumptions\<close>
  named_theorems l_asm_rules \<open>Rules to be tried for discharging locale assumptions\<close>

  ML \<open>
    fun try_lasms_hard ctxt = let
      fun try_hard thm = 
        CAN' (resolve_tac ctxt [thm]) THEN'
        SOLVED' (Method.insert_tac ctxt [thm] THEN_ALL_NEW SELECT_GOAL (auto_tac ctxt))

      val thms = Named_Theorems.get ctxt @{named_theorems l_asm_rules}

      val try_all = SOLVED' (resolve_tac ctxt thms THEN_ALL_NEW assume_tac ctxt)
      val try_all_hard = FIRST' (map try_hard thms)

    in
      TRY o (FIRST' [try_all, SOLVED' (SELECT_GOAL (auto_tac ctxt)), try_all_hard])
    end
    \<close>

  method_setup try_lasms = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (try_lasms_hard ctxt))\<close> 
    \<open>Try to solve assumption similar to theorem in \<open>l_asm_rules\<close>\<close>



    (*
      (Still) ad-hoc hack to remove ghost variables.
      TODO:
        Automate case-splitting
        Declare variables as ghost, and only get rid of assertions and invariants containing declared ghost variables.
          warn if not all ghost variables could be removed!

    *)
    named_theorems_rev remove_ghost_rules \<open>Rules to remove ghost variables\<close>
    ML \<open>
      local
        fun is_no_comb_leq @{mpat (typs) "Trueprop (_\<le>(?t::_ nres))"} = let
          val (_,args) = strip_comb t
          val Ts = map fastype_of args
          fun is_nres_type (Type(@{type_name nres},_)) = true | is_nres_type _ = false
        in
          not (exists (exists_subtype is_nres_type) Ts)
        end
          | is_no_comb_leq _ = false

      in
        fun no_comb_refl_tac ctxt = CONCL_COND' is_no_comb_leq THEN' resolve_tac ctxt @{thms order_refl}
      end  

      fun remove_ghost_step_tac ctxt = let
        val thms = Named_Theorems_Rev.get ctxt @{named_theorems_rev remove_ghost_rules}
      in
        resolve_tac ctxt thms ORELSE' match_tac ctxt @{thms conjI impI allI} ORELSE' no_comb_refl_tac ctxt
      end

      fun remove_ghost_tac ctxt = REPEAT_ALL_NEW (remove_ghost_step_tac ctxt)

    \<close>

    lemma bind_removeg[remove_ghost_rules]:
      fixes m m' :: "'a nres"
      shows "\<lbrakk>m\<le>m'; \<And>x. f x \<le> f' x\<rbrakk> \<Longrightarrow> do { x\<leftarrow>m; f x } \<le> do { x\<leftarrow>m'; f' x}"
      by (rule Refine_Basic.bind_mono)

    lemma Let_removeg[remove_ghost_rules]: 
      "(\<And>x. f x \<le> f' x) \<Longrightarrow> (let x=t in f x) \<le> (let x=t in f' x)" by simp

    lemma [remove_ghost_rules]:
      assumes "\<And>a b. f a b \<le> f' a b"
      shows "(case p of (a,b) \<Rightarrow> f a b) \<le> (case p of (a,b) \<Rightarrow> f' a b)"
      using assms by (cases p) auto

    lemma [remove_ghost_rules]:
      assumes "fn \<le> fn'" "\<And>v. fv v \<le> fv' v"
      shows "(case x of None \<Rightarrow> fn | Some v \<Rightarrow> fv v) \<le> (case x of None \<Rightarrow> fn' | Some v \<Rightarrow> fv' v)"
      using assms by (auto split: option.split)

    lemma [remove_ghost_rules]:
      "\<lbrakk> t \<le> t'; e \<le> e' \<rbrakk> \<Longrightarrow> (if b then t else e) \<le> (if b then t' else e')"
      by auto
      

    (* To be manually instantiated, to remove invariants and assertions *)  
    lemma FOREACHci_removeg: 
      "\<lbrakk>\<And>x s. f x s \<le> f' x s\<rbrakk> \<Longrightarrow> FOREACHc S c f \<sigma> \<le> FOREACHci I S c f' \<sigma>"
      apply (rule refine_IdD)
      apply (refine_rcg inj_on_id) 
      by auto

    lemma ASSERT_removeg: "f \<le> f' () \<Longrightarrow> f \<le> ASSERT \<Phi>\<bind>f'" by (cases \<Phi>) auto






  (* TODO: Move *)  
  lemma conc_fun_R_mono:
    assumes "R \<subseteq> R'"
    shows "\<Down>R M \<le> \<Down>R' M"
    using assms
    by (auto simp: pw_le_iff refine_pw_simps)



    (* TODO: Move *)
    
    lemma nfoldli_refine[refine]:
      assumes "(li, l) \<in> \<langle>S\<rangle>list_rel"
        and "(si, s) \<in> R"
        and CR: "(ci, c) \<in> R \<rightarrow> bool_rel"
        and [refine]: "\<And>xi x si s. \<lbrakk> (xi,x)\<in>S; (si,s)\<in>R; c s \<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
      shows "nfoldli li ci fi si \<le> \<Down> R (nfoldli l c f s)"
      using assms(1,2)
    proof (induction arbitrary: si s rule: list_rel_induct)
      case Nil thus ?case by simp
    next
      case (Cons xi x li l) 
      note [refine] = Cons

      show ?case
        apply (simp split del: split_if)
        apply refine_rcg
        using CR Cons.prems by (auto dest: fun_relD)
    qed    

    (* Refine, establishing additional invariant *)
    lemma nfoldli_invar_refine:
      assumes "(li,l)\<in>\<langle>S\<rangle>list_rel"
      assumes "(si,s)\<in>R"
      assumes "I [] li si"
      assumes COND: "\<And>l1i l2i l1 l2 si s. \<lbrakk>
        li=l1i@l2i; l=l1@l2; (l1i,l1)\<in>\<langle>S\<rangle>list_rel; (l2i,l2)\<in>\<langle>S\<rangle>list_rel; 
        I l1i l2i si; (si,s)\<in>R\<rbrakk> \<Longrightarrow> (ci si, c s)\<in>bool_rel"
      assumes INV: "\<And>l1i xi l2i si. \<lbrakk>li=l1i@xi#l2i; I l1i (xi#l2i) si\<rbrakk> \<Longrightarrow> fi xi si \<le>\<^sub>n SPEC (I (l1i@[xi]) l2i)"
      assumes STEP: "\<And>l1i xi l2i l1 x l2 si s. \<lbrakk>
        li=l1i@xi#l2i; l=l1@x#l2; (l1i,l1)\<in>\<langle>S\<rangle>list_rel; (xi,x)\<in>S; (l2i,l2)\<in>\<langle>S\<rangle>list_rel; 
        I l1i (xi#l2i) si; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
      shows "nfoldli li ci fi si \<le> \<Down>R (nfoldli l c f s)"
    proof -
      {
        have [refine_dref_RELATES]: "RELATES R" "RELATES S" by (auto simp: RELATES_def)

        note [refine del] = nfoldli_refine

        fix l1i l2i l1 l2 si s
        assume "(l2i,l2) \<in> \<langle>S\<rangle>list_rel" "(l1i,l1) \<in> \<langle>S\<rangle>list_rel"
        and "li=l1i@l2i" "l=l1@l2"
        and "(si,s)\<in>R" "I l1i l2i si"
        hence "nfoldli l2i ci fi si \<le> \<Down>R (nfoldli l2 c f s)"
        proof (induction arbitrary: si s l1i l1 rule: list_rel_induct)
          case Nil thus ?case by auto
        next  
          case (Cons xi x l2i l2)

          show ?case
            apply (simp split del: split_if)
            apply (refine_rcg bind_refine')
            apply (refine_dref_type)
            subgoal using COND[of l1i "xi#l2i" l1 "x#l2" si s] Cons.prems Cons.hyps by auto
            subgoal apply (rule STEP) using Cons.prems Cons.hyps by auto
            subgoal for si' s'
              thm Cons.IH
              apply (rule Cons.IH[of "l1i@[xi]" "l1@[x]"])
              using Cons.prems Cons.hyps
              apply (auto simp: list_rel_append1) apply force
              using INV[of l1i xi l2i si]
              by (auto simp: pw_leof_iff)
            subgoal using Cons.prems by simp
            done
        qed
      }
      from this[of li l "[]" "[]" si s] assms(1,2,3) show ?thesis by auto
    qed

    
    lemma nfoldli_leof_rule:
      assumes I0: "I [] l0 \<sigma>0"
      assumes IS: "\<And>x l1 l2 \<sigma>. \<lbrakk> l0=l1@x#l2; I l1 (x#l2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le>\<^sub>n SPEC (I (l1@[x]) l2)"
      assumes FNC: "\<And>l1 l2 \<sigma>. \<lbrakk> l0=l1@l2; I l1 l2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
      assumes FC: "\<And>\<sigma>. \<lbrakk> I l0 [] \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
      shows "nfoldli l0 c f \<sigma>0 \<le>\<^sub>n SPEC P"
    proof -
      {
        fix l1 l2 \<sigma>
        assume "l0=l1@l2" "I l1 l2 \<sigma>"
        hence "nfoldli l2 c f \<sigma> \<le>\<^sub>n SPEC P"
        proof (induction l2 arbitrary: l1 \<sigma>)
          case Nil thus ?case
            apply simp
            apply (cases "c \<sigma>")
            applyS (rule FC; auto)
            applyS (rule FNC[of l1 "[]"]; auto) 
            done
        next
          case (Cons x l2) 
          note [refine_vcg] = Cons.IH[of "l1@[x]",THEN leof_trans] IS[of l1 x l2 \<sigma>,THEN leof_trans]

          show ?case
            apply (simp split del: split_if)
            apply refine_vcg
            using Cons.prems FNC by auto
        qed
      } from this[of "[]" l0 \<sigma>0] I0 show ?thesis by auto
    qed  
            

    (* TODO: Move! *)  
    lemma prod_case_refine:  
      assumes "(p',p)\<in>R1\<times>\<^sub>rR2"
      assumes "\<And>x1' x2' x1 x2. \<lbrakk> p'=(x1',x2'); p=(x1,x2); (x1',x1)\<in>R1; (x2',x2)\<in>R2\<rbrakk> \<Longrightarrow> f' x1' x2' \<le> \<Down>R (f x1 x2)"
      shows "(case p' of (x1',x2') \<Rightarrow> f' x1' x2') \<le>\<Down>R (case p of (x1,x2) \<Rightarrow> f x1 x2)"
      using assms by (auto split: prod.split)



  definition "FOREACHcd S c f \<sigma> \<equiv> do {
    ASSERT (finite S);
    l \<leftarrow> SPEC (\<lambda>l. set l = S);
    nfoldli l c f \<sigma>
  }"

  thm nfoldli_rule

  lemma FOREACHcd_rule:
    assumes "finite S\<^sub>0"
    assumes I0: "I {} S\<^sub>0 \<sigma>\<^sub>0"
    assumes STEP: "\<And>S1 S2 x \<sigma>. \<lbrakk> S\<^sub>0 = insert x (S1\<union>S2); I S1 (insert x S2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (insert x S1) S2)"
    assumes INTR: "\<And>S1 S2 \<sigma>. \<lbrakk> S\<^sub>0 = S1\<union>S2; I S1 S2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> \<Phi> \<sigma>"
    assumes COMPL: "\<And>\<sigma>. \<lbrakk> I S\<^sub>0 {} \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> \<Phi> \<sigma>"
    shows "FOREACHcd S\<^sub>0 c f \<sigma>\<^sub>0 \<le> SPEC \<Phi>"
    unfolding FOREACHcd_def
    apply refine_vcg
    apply fact
    apply (rule nfoldli_rule[where I = "\<lambda>l1 l2 \<sigma>. I (set l1) (set l2) \<sigma>"])
    subgoal using I0 by auto
    subgoal using STEP by auto
    subgoal using INTR by auto
    subgoal using COMPL by auto
    done
  
  definition FOREACHcdi 
    :: "('a set \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool) 
      \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b nres) \<Rightarrow> 'b \<Rightarrow> 'b nres"
    where
    "FOREACHcdi I \<equiv> FOREACHcd"  

  lemma FOREACHcdi_rule[refine_vcg]:
    assumes "finite S\<^sub>0"
    assumes I0: "I {} S\<^sub>0 \<sigma>\<^sub>0"
    assumes STEP: "\<And>S1 S2 x \<sigma>. \<lbrakk> S\<^sub>0 = insert x (S1\<union>S2); I S1 (insert x S2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (insert x S1) S2)"
    assumes INTR: "\<And>S1 S2 \<sigma>. \<lbrakk> S\<^sub>0 = S1\<union>S2; I S1 S2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> \<Phi> \<sigma>"
    assumes COMPL: "\<And>\<sigma>. \<lbrakk> I S\<^sub>0 {} \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> \<Phi> \<sigma>"
    shows "FOREACHcdi I S\<^sub>0 c f \<sigma>\<^sub>0 \<le> SPEC \<Phi>"
    unfolding FOREACHcdi_def
    using assms
    by (rule FOREACHcd_rule)

  lemma map_in_list_rel_conv: 
    shows "(l, map \<alpha> l) \<in> \<langle>br \<alpha> I\<rangle>list_rel \<longleftrightarrow> (\<forall>x\<in>set l. I x)"
    by (induction l) (auto simp: in_br_conv)


  lemma br_set_rel_alt: "(s',s)\<in>\<langle>br \<alpha> I\<rangle>set_rel \<longleftrightarrow> (s=\<alpha>`s' \<and> (\<forall>x\<in>s'. I x))"  
    by (auto simp: set_rel_def br_def)

  lemma FOREACHcd_refine[refine]:
    assumes [simp]: "finite s'"
    assumes S: "(s',s)\<in>\<langle>S\<rangle>set_rel"
    assumes SV: "single_valued S"
    assumes R0: "(\<sigma>',\<sigma>)\<in>R"
    assumes C: "\<And>\<sigma>' \<sigma>. (\<sigma>',\<sigma>)\<in>R \<Longrightarrow> (c' \<sigma>', c \<sigma>)\<in>bool_rel"
    assumes F: "\<And>x' x \<sigma>' \<sigma>. \<lbrakk>(x', x) \<in> S; (\<sigma>', \<sigma>) \<in> R\<rbrakk>
       \<Longrightarrow> f' x' \<sigma>' \<le> \<Down> R (f x \<sigma>)"
    shows "FOREACHcd s' c' f' \<sigma>' \<le> \<Down>R (FOREACHcdi I s c f \<sigma>)"
  proof -
    have [refine_dref_RELATES]: "RELATES S" by (simp add: RELATES_def)
  
    from SV obtain \<alpha> I where [simp]: "S=br \<alpha> I" by (rule single_valued_as_brE)
    with S have [simp]: "s=\<alpha>`s'" and [simp]: "\<forall>x\<in>s'. I x" 
      by (auto simp: br_set_rel_alt)
    
    show ?thesis
      unfolding FOREACHcd_def FOREACHcdi_def
      apply refine_rcg
      apply refine_dref_type
      subgoal by simp
      subgoal
        apply (auto simp: pw_le_iff refine_pw_simps)
        using S
        apply (rule_tac x="map \<alpha> x" in exI)
        apply (auto simp: map_in_list_rel_conv)
        done
      subgoal using R0 by auto
      subgoal using C by auto  
      subgoal using F by auto
      done
  qed    
      
  lemma FOREACHc_refines_FOREACHcd_aux:
    shows "FOREACHc s c f \<sigma> \<le> FOREACHcd s c f \<sigma>"
    unfolding FOREACHc_def FOREACHci_def FOREACHoci_by_LIST_FOREACH LIST_FOREACH'_eq
      LIST_FOREACH'_def FOREACHcd_def it_to_sorted_list_def
    apply (rule refine_IdD)  
    apply (refine_rcg)
    apply refine_dref_type
    apply auto
    done
      
  lemmas FOREACHc_refines_FOREACHcd[refine]
    = order_trans[OF FOREACHc_refines_FOREACHcd_aux FOREACHcd_refine]


section \<open>Abstraction 1 (Partial Assignment)\<close>

  definition "prop_unit_spec F A \<equiv> SPEC (\<lambda>A'. 
      (A,A')\<in>(prop_unit_R F)\<^sup>* 
    \<and> (A'\<notin>Domain (prop_unit_R F) \<or> (\<exists>C\<in>F. is_conflict_clause A' C))
  )"

  definition "has_conflict_spec F A \<equiv> RETURN (\<exists>C\<in>F. is_conflict_clause A C)"

  text \<open>No conflict and units propagated. Precondition for most operations. \<close>
  definition "up_no_conflict F A \<equiv> 
      (\<forall>C\<in>F. \<not>is_conflict_clause A C \<and> \<not>is_unit_clause A C)"



  lemma prop_unit_spec_correct[THEN order_trans, refine_vcg]: 
    "prop_unit_spec F A \<le> SPEC (\<lambda>A'. equiv' F A A' 
      \<and> ((\<forall>C\<in>F. \<not>is_unit_clause A' C) \<or> (\<exists>C\<in>F. is_conflict_clause A' C))
    )"
    unfolding prop_unit_spec_def
    by (auto intro: prop_unit_R_equiv)

  definition "has_rup_spec F A C \<equiv> do {
    ASSERT (up_no_conflict F A);
    ASSERT (finite C);
    if \<exists>l\<in>C. sem_lit' l A = Some True \<or> neg_lit l\<in>C then
      RETURN True
    else do {
      let A = assign_all_negated A C;
      A \<leftarrow> prop_unit_spec F A;
      RETURN (\<exists>C\<in>F. is_conflict_clause A C)
    }
  }"

  (* TODO: Move *)
  lemma tautology: "\<lbrakk>l\<in>C; neg_lit l \<in> C\<rbrakk> \<Longrightarrow> sem_clause C \<sigma>"
    by (cases "sem_lit l \<sigma>"; cases l; force simp: sem_clause_def)

  lemma implied_taut: "\<lbrakk>l\<in>C; neg_lit l \<in> C\<rbrakk> \<Longrightarrow> implied_clause F A C"
    unfolding implied_clause_def models'_def using tautology[of l C]
    by auto


  lemma has_rup_spec_correct[THEN order_trans, refine_vcg]: 
    "\<lbrakk>up_no_conflict F A; finite C\<rbrakk> \<Longrightarrow> has_rup_spec F A C \<le> SPEC (\<lambda>r. r \<longrightarrow> implied_clause F A C)"
    unfolding has_rup_spec_def
    apply (refine_vcg)
    subgoal by (auto 0 3 intro: true_clause_implied simp: sem_clause'_true_conv implied_taut) []
    subgoal by (auto simp: abs_rup_criterion conflict_clause_imp_no_models implied_is_redundant equiv'_def)
    done  

  abbreviation "has_rat_fe_invar F A C reslit 
    \<equiv> (\<lambda>it1 it2 flag. flag \<longrightarrow> (\<forall>D\<in>it1. neg_lit reslit \<in> D \<longrightarrow> implied_clause F A (D-{neg_lit reslit} \<union> C)))"  




  definition "has_rat_spec F A C \<equiv> do {
    ASSERT (up_no_conflict F A);
    if C={} then RETURN False
    else do {
      reslit \<leftarrow> OBTAIN (\<lambda>l. l\<in>C);
      if sem_lit' reslit A \<noteq> Some False then do {
        FOREACHcdi (has_rat_fe_invar F A C reslit) 
          { D\<in>F. neg_lit reslit \<in> D } (\<lambda>flag. flag) (\<lambda>D _. do {
            has_rup_spec F A (D-{neg_lit reslit} \<union> C)
        }) True
      } else RETURN False
    }
  }"  

  lemma has_rat_spec_correct[THEN order_trans, refine_vcg]:
    "\<lbrakk>finite F; finite C; \<forall>C'\<in>F. finite C'; up_no_conflict F A\<rbrakk> \<Longrightarrow> has_rat_spec F A C \<le> SPEC (\<lambda>r. r \<longrightarrow> redundant_clause F A C)"
    unfolding has_rat_spec_def
    apply refine_vcg
    apply vc_solve
    subgoal by (auto)
    subgoal by auto
    subgoal by (blast intro: abs_rat_criterion)
    done

  definition "has_rup_or_rat_spec F A C \<equiv> do {
    ASSERT (up_no_conflict F A);
    rup \<leftarrow> has_rup_spec F A C;
    if rup then RETURN True 
    else do {
      rat \<leftarrow> has_rat_spec F A C;
      RETURN rat
    }
  }"


  lemma has_rup_or_rat_correct[THEN order_trans, refine_vcg]:
    "\<lbrakk>finite F; finite C; \<forall>C'\<in>F. finite C'; up_no_conflict F A\<rbrakk> \<Longrightarrow> has_rup_or_rat_spec F A C \<le> SPEC (\<lambda>r. r \<longrightarrow> redundant_clause F A C)"
    unfolding has_rup_or_rat_spec_def
    by refine_vcg (auto simp: implied_is_redundant)

  datatype 'a proof_step = Add "'a clause" | Del "'a clause"

  lemma proof_step_rule[refine_vcg]:
    assumes "\<And>C. s=Add C \<Longrightarrow> fa C \<le> SPEC \<Phi>"
    assumes "\<And>C. s=Del C \<Longrightarrow> fd C \<le> SPEC \<Phi>"
    shows "(case s of Add C \<Rightarrow> fa C | Del C \<Rightarrow> fd C) \<le> SPEC \<Phi>"
    using assms by (cases s) auto



  datatype verify_result = UNSAT | ERROR

  definition "add_clause C F A \<equiv> do {
    if is_conflict_clause A C then
      RETURN (True,F,A)
    else if is_unit_clause A C then do {
      l \<leftarrow> OBTAIN (\<lambda>l. is_unit_lit A C l);
      let A = assign_lit A l;
      RETURN (False,F,A)
    } else if sem_clause' C A = Some True then
      RETURN (False,F,A)
    else
      RETURN (False,insert C F,A)
  }"


  definition "load_clauses F\<^sub>0 \<equiv> do {
    let F = {};
    let A = Map.empty;
    nfoldli F\<^sub>0 (\<lambda>(conflict,_,_). \<not>conflict) (\<lambda>C (_,F,A). 
      add_clause C F A
    ) (False,F,A)
  }"

  lemma models'_empty[simp]: "models' {} Map.empty = UNIV"
    unfolding models'_def by auto

  lemma unit_clause_models_conv:
    assumes CL: "C\<in>F"
    assumes UNIT: "is_unit_lit A C l"  
    assumes "sem_clause' C A \<noteq> Some False"
    shows "models' F (assign_lit A l) = models' F A \<inter> {\<sigma>. sem_clause C \<sigma>}"
    using assms
    apply (safe; clarsimp simp: models'_def is_unit_lit_def)
  proof -  
    fix \<sigma>
    assume 
      CNF: "sem_clause' C A \<noteq> Some False" 
      and "l \<in> C" 
      and HOLDS: "sem_cnf F \<sigma>" 
      and UNDEC: "sem_lit' l A = None"
      and FALSE: "sem_clause' (C - {l}) A = Some False"

    {
      assume A_COMPAT: "compat_assignment (assign_lit A l) \<sigma>" 
  
      show "compat_assignment A \<sigma>"
        using A_COMPAT UNDEC
        apply (clarsimp simp: compat_assignment_def; safe)
        apply (cases l; simp; metis option.distinct(1))
        apply (cases l; simp; metis option.distinct(1))
        done
        
      show "sem_clause C \<sigma>" 
        using A_COMPAT UNIT compat_clause unit_clause_assign_dec by blast
    }
      
    {
      assume COMPAT: "compat_assignment A \<sigma>"

      from CL HOLDS have "sem_clause C \<sigma>" by (auto simp: sem_cnf_def)
      moreover from compat_lit[OF COMPAT] FALSE have "\<forall>ll\<in>C. ll\<noteq>l \<longrightarrow> \<not>sem_lit ll \<sigma>"
        by (auto simp: sem_clause'_false_conv)
      ultimately have "sem_lit l \<sigma>" by (auto simp: sem_clause_def)

      thus "compat_assignment (assign_lit A l) \<sigma>"  
        using COMPAT 
        by (cases l) (auto simp: compat_assignment_def)
    }
  qed

  lemma compat_assign_lit1: 
    assumes "sem_lit' l A = None"
    assumes "compat_assignment (assign_lit A l) \<sigma>"
    shows "compat_assignment A \<sigma>"
    using assms
    unfolding compat_assignment_def
    apply (cases l; clarsimp split: split_if_asm)
    apply (metis option.distinct(1))+
    done

  lemma compat_assign_lit2: 
    assumes "compat_assignment A \<sigma>"
    assumes "sem_lit l \<sigma>"
    shows "compat_assignment (assign_lit A l) \<sigma>"
    using assms
    unfolding compat_assignment_def
    apply (cases l; auto split: split_if_asm)
    done


  lemma unit_models_assign:
    assumes UNIT: "is_unit_lit A C l"
    shows "models' F (assign_lit A l) = models' (insert C F) A"
  proof safe
    from UNIT have 
      LIC: "l\<in>C" 
      and SL: "sem_lit' l A = None" 
      and SO: "sem_clause' (C-{l}) A = Some False"
      unfolding is_unit_lit_def by auto

    fix \<sigma>

    {  
      assume "\<sigma> \<in> models' F (assign_lit A l)"
      hence COMPAT: "compat_assignment (assign_lit A l) \<sigma>" and SEM: "sem_cnf F \<sigma>"
        by (auto simp: models'_def)

      from SL COMPAT have COMPAT': "compat_assignment A \<sigma>" by (rule compat_assign_lit1)
    
      from COMPAT have "sem_lit l \<sigma>" unfolding compat_assignment_def 
        by (cases l) (auto split: split_if_asm)

      with LIC SL have "sem_clause C \<sigma>" unfolding sem_clause_def by auto
      with COMPAT' SEM show "\<sigma> \<in> models' (insert C F) A"
        unfolding models'_def by auto
    }
    {
      assume "\<sigma> \<in> models' (insert C F) A"
      hence COMPAT: "compat_assignment A \<sigma>" and SC: "sem_clause C \<sigma>" and SF: "sem_cnf F \<sigma>"
        by (auto simp: models'_def)
        
      from SC SO compat_clause[OF COMPAT] have "sem_lit l \<sigma>"
        by (auto simp: sem_clause_def)
        
      with COMPAT have "compat_assignment (assign_lit A l) \<sigma>"
        by (rule compat_assign_lit2)
      with SF show "\<sigma> \<in> models' F (assign_lit A l)" by (auto simp: models'_def)
    }
  qed  

  lemma true_models_insert: 
    assumes TRUE: "sem_clause' C A = Some True"
    shows "models' (insert C F) A = models' F A"
    using assms implied_clause_def true_clause_implied by blast

  lemma add_clause_correct[THEN order_trans, refine_vcg]: 
    "\<lbrakk>finite F; \<forall>C'\<in>F. finite C'; finite C\<rbrakk> \<Longrightarrow> add_clause C F A \<le> SPEC (\<lambda>
      (True,F',_) \<Rightarrow> finite F' \<and> (\<forall>C'\<in>F'. finite C') \<and> models' (insert C F) A = {}
    | (False,F',A') \<Rightarrow> finite F' \<and> (\<forall>C'\<in>F'. finite C') \<and> models' F' A' = models' (insert C F) A
    )"
    unfolding add_clause_def
    apply (refine_vcg)
    apply vc_solve
    subgoal by (meson conflict_clause_imp_no_models insertI1)
    subgoal by (auto simp: is_unit_clause_def)
    subgoal by (auto simp: unit_models_assign)
    subgoal by (auto simp: true_models_insert)
    done
    

  lemma load_clauses_correct[THEN order_trans, refine_vcg]: 
    assumes "\<forall>C\<in>set F\<^sub>0. finite C"
    shows "load_clauses F\<^sub>0 \<le> SPEC (\<lambda>(conf,F,A). finite F \<and> (\<forall>C\<in>F. finite C) \<and>
      (conf \<longrightarrow> \<not>sat (set F\<^sub>0)) \<and>
      (\<not>conf \<longrightarrow> sat' F A = sat (set F\<^sub>0) ))"
    unfolding load_clauses_def
    using assms
    apply (refine_vcg
      nfoldli_rule[where I="\<lambda>F\<^sub>r _ (conf,F,A). finite F \<and> (\<forall>C\<in>F. finite C) \<and>
        (conf \<longrightarrow> \<not>sat (set F\<^sub>0)) \<and>
        (\<not>conf \<longrightarrow> models' F A = {\<sigma>. sem_cnf (set F\<^sub>r) \<sigma>})"]
    )
    apply (vc_solve del: notI solve: asm_rl[of "finite _"] split: bool.splits)
    subgoal by (auto simp: models'_def sat_def image_Un)  
    subgoal by (auto simp: models'_def)
    subgoal by (auto simp: sat'_def sat_def)
    done    
     
  definition "maybe_delete C F A \<equiv> do {
    ASSERT (up_no_conflict F A);
    F \<leftarrow> RES {F-{C},F};
    RETURN (F,A)
  }"

  lemma maybe_delete_correct[THEN order_trans, refine_vcg]: 
    "\<lbrakk>up_no_conflict F A; finite F; \<forall>C\<in>F. finite C\<rbrakk> 
    \<Longrightarrow> maybe_delete C F A \<le> SPEC (\<lambda>(F',A'). models' F A \<subseteq> models' F' A' \<and> finite F' \<and> (\<forall>C'\<in>F'. finite C') \<and> up_no_conflict F' A')"
    unfolding maybe_delete_def
    apply refine_vcg
    apply (auto simp: models'_def sem_cnf_def up_no_conflict_def)
    done


  definition "verify F prf \<equiv> do {
    (conf,F,A) \<leftarrow> load_clauses F;      (* Load clauses *)

    if conf then RETURN UNSAT          (* This may already reveal conflict *) 
    else do {
      A \<leftarrow> prop_unit_spec F A;         (* Propagate units *)
      conf \<leftarrow> has_conflict_spec F A;   (* Check for conflicts *)
  
      if conf then
        RETURN UNSAT (* Conflict from initial clauses by unit propagation *)
      else do {  
        (* No conflicts initially. Iterate over proof *)
        (flag,F,A) \<leftarrow> nfoldli prf (\<lambda>(flag,_,_). flag=0) (\<lambda>s (_,F,A). do {
          case s of
            Add C \<Rightarrow> do {
              (* Check if add-clause has RUP or RAT *)
              ror \<leftarrow> has_rup_or_rat_spec F A C;
              if ror then do {
                (* Add the clause. This may find the clause to be a conflict clause. *)
                (conf,F,A) \<leftarrow> add_clause C F A;
                if conf then RETURN (1,F,A) (* Added conflict clause *)
                else do {
                  (* If no immediate conflict, do unit propagation *)
                  A \<leftarrow> prop_unit_spec F A;
                  conf \<leftarrow> has_conflict_spec F A;
                  if conf then 
                    RETURN (1,F,A) (* Unit propagation found a conflict *)
                  else
                    RETURN (0,F,A) (* Unit propagation did not find a conflict *)
                }
              } else
                RETURN (-1, F, A) (* Attempt to add clause without RUP or RAT *)
            }
          | Del C \<Rightarrow> do {
              (F,A) \<leftarrow> maybe_delete C F A;
              RETURN (0,F,A)
            }  
        }) (0::int,F,A);

        if flag = 1 then RETURN UNSAT
        else RETURN ERROR
      }
    }  
  }"



  lemma verify_correct: 
    assumes "\<forall>C\<in>set F. finite C"
    assumes "\<forall>s\<in>set prf. case s of Add C \<Rightarrow> finite C | Del C \<Rightarrow> finite C"
    shows "verify F prf \<le> SPEC (\<lambda>r. r=UNSAT \<longrightarrow> \<not>sat (set F))"
    unfolding verify_def has_conflict_spec_def
    using assms
    apply (refine_vcg nfoldli_rule[where I="\<lambda>_ _ (flag,F',A'). finite F' \<and> (\<forall>C\<in>F'. finite C) 
        \<and> (flag=0 \<longrightarrow> up_no_conflict F' A' \<and> (sat (set F) \<longrightarrow> sat' F' A'))
        \<and> (flag=1 \<longrightarrow> \<not>sat (set F))"
        ])
    apply (vc_solve 
      simp: equiv'_map_empty_sym 
      del: notI
      solve: asm_rl[of "finite _"]
      )
    apply (clarsimp_all simp: sat'_equiv)
    subgoal
      by (auto simp: sat'_def dest: conflict_clause_imp_no_models)
    subgoal by (auto simp: up_no_conflict_def)  
    subgoal  
      by (simp add: redundant_clause_def sat'_def)
    subgoal  
      by (simp add: conflict_clause_imp_no_models equiv'_def redundant_clause_def sat'_def)
    subgoal by (auto simp: up_no_conflict_def)
    subgoal  
      by (metis add_redundant_sat_iff sat'_def sat'_equiv)
    subgoal by (auto simp: sat'_def)
    done

section \<open>Abstraction 2 (Clause DB)\<close>

  type_synonym 'idx proof_step2 = "bool \<times> 'idx"

  locale abs_clause_db_defs =
    fixes DB :: "'idx \<rightharpoonup> 'a clause"
  begin  
    abbreviation "CL i \<equiv> the (DB i)"

    definition "ic_rel \<equiv> br CL (\<lambda>i. i\<in>dom DB)"
    definition "F_rel \<equiv> br (image CL) (\<lambda>F. F\<subseteq>dom DB)"

    definition "ps_rel \<equiv> 
        { ((False,i), Add C) | i C. (i,C)\<in>ic_rel }
      \<union> { ((True,i), Del C) | i C. (i,C)\<in>ic_rel }"

    lemma ps_rel_simps[simp]: 
      "((False,i),y)\<in>ps_rel \<longleftrightarrow> (\<exists>C. y = Add C \<and> (i,C)\<in>ic_rel)"
      "((True,i),y)\<in>ps_rel \<longleftrightarrow> (\<exists>C. y = Del C \<and> (i,C)\<in>ic_rel)"
      "(x,proof_step.Add C)\<in>ps_rel \<longleftrightarrow> (\<exists>i. x = (False,i) \<and> (i,C)\<in>ic_rel)"
      "(x,proof_step.Del C)\<in>ps_rel \<longleftrightarrow> (\<exists>i. x = (True,i) \<and> (i,C)\<in>ic_rel)"
      unfolding ps_rel_def by auto


  end

  locale abs_clause_db = abs_clause_db_defs +
    assumes finite_DB[simp, intro!]: "finite (dom DB)"
    assumes finite_clauses: "C\<in>ran DB \<Longrightarrow> finite C"
  begin  

    lemma finite_clauses'[simp, intro]: "i\<in>dom DB \<Longrightarrow> finite (CL i)"
      using finite_clauses by (force intro: ranI)
    
    definition "add_clause2 i F A \<equiv> do {
      ASSERT (i\<in>dom DB \<and> i\<notin>F);
      let C = CL i;
      if is_conflict_clause A C then
        RETURN (True,F,A)
      else if is_unit_clause A C then do {
        l \<leftarrow> OBTAIN (\<lambda>l. is_unit_lit A C l);
        let A = assign_lit A l;
        RETURN (False,F,A)
      } else if sem_clause' C A = Some True then
        RETURN (False,F,A)
      else
        RETURN (False,insert i F,A)
    }"


    lemma add_clause2_refine[refine]: "\<lbrakk> (i,C)\<in>ic_rel; (Fi,F)\<in>F_rel; (Ai,A)\<in>Id; i\<notin>Fi \<rbrakk> \<Longrightarrow>
      add_clause2 i Fi Ai \<le> \<Down>(bool_rel \<times>\<^sub>r F_rel \<times>\<^sub>r Id) (add_clause C F A)"
      unfolding add_clause2_def add_clause_def
      apply refine_rcg
      apply refine_dref_type
      apply (auto simp: F_rel_def br_def ic_rel_def)
      done

    definition "load_clauses2 F\<^sub>0 \<equiv> do {
      let F = {};
      let A = Map.empty;
      nfoldli F\<^sub>0 (\<lambda>(conflict,_,_). \<not>conflict) (\<lambda>C (_,F,A). 
        add_clause2 C F A
      ) (False,F,A)
    }"
        

    lemma load_clauses2_refine[refine]: 
      "\<lbrakk> (F0i,F0)\<in>\<langle>ic_rel\<rangle>list_rel; distinct F0i \<rbrakk> \<Longrightarrow> load_clauses2 F0i \<le> \<Down>(bool_rel \<times>\<^sub>r F_rel \<times>\<^sub>r Id) (load_clauses F0)"
      unfolding load_clauses2_def load_clauses_def
      apply (refine_rcg nfoldli_invar_refine[where I="\<lambda>l0 l1 (_,F,_). distinct (l0@l1) \<and> F\<subseteq>set l0"])
      apply assumption
      apply vc_solve
      apply (simp add: F_rel_def in_br_conv)
      subgoal
        unfolding add_clause2_def
        apply refine_vcg
        apply auto
        done
      subgoal by auto []
      done
      
    definition "delete_clause2 i F A \<equiv> do {
      RETURN (F-{i},A)
    }"

    lemma delete_clause2_refine[refine]: 
      "\<lbrakk> (i,C)\<in>ic_rel; (Fi,F)\<in>F_rel; (Ai,A)\<in>Id \<rbrakk> 
      \<Longrightarrow> delete_clause2 i Fi Ai \<le> \<Down>(F_rel \<times>\<^sub>r Id) (maybe_delete C F A)"
      unfolding delete_clause2_def maybe_delete_def
      apply (simp add: pw_le_iff refine_pw_simps)
      apply (auto simp: ic_rel_def in_br_conv F_rel_def)
      done

    definition "prop_unit_spec2 F A \<equiv> 
      SPEC (\<lambda>A'. 
          (A,A')\<in>(prop_unit_R (CL`F))\<^sup>* 
        \<and> (A'\<notin>Domain (prop_unit_R (CL`F)) \<or> (\<exists>i\<in>F. is_conflict_clause  A' (CL i)))
      )"

    lemma prop_unit_spec2_refine[refine]: "\<lbrakk> (Fi,F)\<in>F_rel; (Ai,A)\<in>Id \<rbrakk> 
      \<Longrightarrow> prop_unit_spec2 Fi Ai \<le> \<Down>Id (prop_unit_spec F A)"  
      unfolding prop_unit_spec2_def prop_unit_spec_def
      apply refine_vcg
      by (auto simp: F_rel_def in_br_conv)

    definition "has_conflict_spec2 F A \<equiv> RETURN (\<exists>i\<in>F. is_conflict_clause A (CL i))"

    lemma has_conflict_spec2_refine[refine]: 
      "\<lbrakk> (Fi,F)\<in>F_rel; (Ai,A)\<in>Id \<rbrakk> \<Longrightarrow> has_conflict_spec2 Fi Ai \<le>\<Down>bool_rel (has_conflict_spec F A)"
      unfolding has_conflict_spec2_def has_conflict_spec_def
      apply refine_rcg
      by (auto simp: F_rel_def in_br_conv)
      
    definition "has_rup2 F A C \<equiv> do {
      ASSERT (up_no_conflict (CL`F) A);
      ASSERT (finite C);
      if \<exists>l\<in>C. sem_lit' l A = Some True \<or> neg_lit l \<in> C then
        RETURN True
      else do {
        let A = assign_all_negated A C;
        A \<leftarrow> prop_unit_spec2 F A;
        RETURN (\<exists>i\<in>F. is_conflict_clause A (CL i))
      }
    }"
     
    lemma has_rup2_refine[refine]: "\<lbrakk> (Fi,F)\<in>F_rel; (Ai,A)\<in>Id; (Ci,C)\<in>Id \<rbrakk> \<Longrightarrow> 
      has_rup2 Fi Ai Ci \<le> \<Down>bool_rel (has_rup_spec F A C)"
      unfolding has_rup2_def has_rup_spec_def
      apply refine_rcg
      apply (auto simp: F_rel_def ic_rel_def in_br_conv)
      done

    definition "has_rat2 F A Ci \<equiv> do {
      ASSERT (up_no_conflict (CL`F) A);
      let C = CL Ci;
      if C={} then RETURN False
      else do {
        reslit \<leftarrow> OBTAIN (\<lambda>l. l\<in>C);
        if sem_lit' reslit A \<noteq> Some False then do {
          FOREACHc  
            { j\<in>F. neg_lit reslit \<in> CL j } (\<lambda>flag. flag) (\<lambda>j _. do {
              has_rup2 F A (CL j-{neg_lit reslit} \<union> C)
          }) True
        } else RETURN False
      }
    }"  

    lemma has_rat2_refine[refine]: 
      assumes "(Fi,F)\<in>F_rel" "(Ai,A)\<in>Id" "(Ci,C)\<in>ic_rel"  
      shows "has_rat2 Fi Ai Ci \<le> \<Down>bool_rel (has_rat_spec F A C)"
    proof -

      have [refine_dref_RELATES]: "RELATES ic_rel" by (simp add: RELATES_def)

      show ?thesis
        unfolding has_rat2_def has_rat_spec_def
        apply (refine_rcg inj_on_id)
        apply refine_dref_type
        using assms
        apply (vc_solve simp: F_rel_def in_br_conv ic_rel_def solve: asm_rl[of "Ex _"])
        subgoal by (auto dest: finite_subset[OF _ finite_DB])
        subgoal by (auto simp: br_set_rel_alt)
        done
    qed    


    definition "has_rup_or_rat2 F A Ci \<equiv> do {
      ASSERT (up_no_conflict (CL`F) A);
      rup \<leftarrow> has_rup2 F A (CL Ci);
      if rup then RETURN True 
      else do {
        rat \<leftarrow> has_rat2 F A Ci;
        RETURN rat
      }
    }"

    lemma has_rup_or_rat2_refine[refine]:
      assumes "(Fi,F)\<in>F_rel" "(Ai,A)\<in>Id" "(Ci,C)\<in>ic_rel"  
      shows "has_rup_or_rat2 Fi Ai Ci \<le> \<Down>bool_rel (has_rup_or_rat_spec F A C)"
      using assms unfolding has_rup_or_rat2_def has_rup_or_rat_spec_def
      apply refine_rcg
      apply (auto simp: F_rel_def ic_rel_def in_br_conv)
      done


  
    definition "verify2 F\<^sub>0 prf \<equiv> do {
      (conf,F,A) \<leftarrow> load_clauses2 F\<^sub>0;     (* Load clauses *)
  
      if conf then RETURN UNSAT           (* This may already reveal conflict *) 
      else do {
        A \<leftarrow> prop_unit_spec2 F A;         (* Propagate units *)
        conf \<leftarrow> has_conflict_spec2 F A;   (* Check for conflicts *)
    
        if conf then
          RETURN UNSAT (* Conflict from initial clauses by unit propagation *)
        else do {  
          (* No conflicts initially. Iterate over proof *)
          (flag,F,A) \<leftarrow> nfoldli prf (\<lambda>(flag,_,_). flag=0) (\<lambda>s (_,F,A). do {
            case s of
              (False,C) \<Rightarrow> do {
                (* Check if add-clause has RUP or RAT *)
                ror \<leftarrow> has_rup_or_rat2 F A C;
                if ror then do {
                  (* Add the clause. This may find the clause to be a conflict clause. *)
                  (conf,F,A) \<leftarrow> add_clause2 C F A;
                  if conf then RETURN (1,F,A) (* Added conflict clause *)
                  else do {
                    (* If no immediate conflict, do unit propagation *)
                    A \<leftarrow> prop_unit_spec2 F A;
                    conf \<leftarrow> has_conflict_spec2 F A;
                    if conf then 
                      RETURN (1,F,A) (* Unit propagation found a conflict *)
                    else
                      RETURN (0,F,A) (* Unit propagation did not find a conflict *)
                  }
                } else
                  RETURN (-1, F, A) (* Attempt to add clause without RUP or RAT *)
              }
            | (True,C) \<Rightarrow> do {
                (F,A) \<leftarrow> delete_clause2 C F A;
                RETURN (0,F,A)
              }  
          }) (0::int,F,A);
  
          if flag = 1 then RETURN UNSAT
          else RETURN ERROR
        }
      }  
    }"

    lemma ps_cases2_refine[refine]:
      assumes "(s',s)\<in>ps_rel"
      assumes "\<And>i C. \<lbrakk>s'=(False,i); s=Add C; (i,C)\<in>ic_rel\<rbrakk> \<Longrightarrow> fa' i \<le>\<Down>R (fa C)"
      assumes "\<And>i C. \<lbrakk>s'=(True,i); s=Del C; (i,C)\<in>ic_rel\<rbrakk> \<Longrightarrow> fd' i \<le>\<Down>R (fd C)"
      shows "(case s' of (False,i) \<Rightarrow> fa' i | (True,i) \<Rightarrow> fd' i)
        \<le> \<Down>R (case s of Add C \<Rightarrow> fa C | Del C \<Rightarrow> fd C)"
      using assms by (auto split: proof_step.split)  

    lemma add_clause2_set_aux[THEN leof_trans]: "add_clause2 i F A \<le>\<^sub>n SPEC (\<lambda>(conf,F',A'). F' \<subseteq> insert i F)"
      unfolding add_clause2_def
      by refine_vcg auto

    lemma load_clauses2_set_aux: "load_clauses2 F\<^sub>0 \<le>\<^sub>n SPEC (\<lambda>(conf,F,A). F \<subseteq> set F\<^sub>0)"  
      unfolding load_clauses2_def
      apply (refine_vcg 
        nfoldli_leof_rule[where I="\<lambda>_ _ (conf,F,A). F \<subseteq> set F\<^sub>0"]
        add_clause2_set_aux
      )
      by auto

    lemma case_bool_leof_rule[refine_vcg]:
      assumes "b \<Longrightarrow> ft \<le>\<^sub>n SPEC \<Phi>"
      assumes "\<not>b \<Longrightarrow> ff \<le>\<^sub>n SPEC \<Phi>"
      shows "(case b of True \<Rightarrow> ft | False \<Rightarrow> ff) \<le>\<^sub>n SPEC \<Phi>"
      using assms by (cases b) auto

    lemma case_bool_refine[refine]:  
      "\<lbrakk> (bi,b)\<in>bool_rel; \<lbrakk>bi;b\<rbrakk> \<Longrightarrow> fti\<le>\<Down>R ft; \<lbrakk>\<not>bi; \<not>b\<rbrakk> \<Longrightarrow> ffi \<le>\<Down>R ff \<rbrakk> 
        \<Longrightarrow> (case bi of True \<Rightarrow> fti | False \<Rightarrow> ffi) \<le> \<Down>R (case b of True \<Rightarrow> ft | False \<Rightarrow> ff)"
      by (cases b; auto)  

    lemma verify2_refine[refine]:
      assumes [refine]: "(F',F)\<in>\<langle>ic_rel\<rangle>list_rel"
      assumes [refine]: "(prf',prf)\<in>\<langle>ps_rel\<rangle>list_rel"
      assumes [simp]: "distinct F'"
      assumes [simp]: "distinct (filter (Not o fst) prf')" 
      assumes PF_DJ: "set (map snd (filter (Not o fst) prf')) \<inter> set F' = {}"
      shows "verify2 F' prf' \<le> \<Down>Id (verify F prf)"
    proof -
      have [refine_dref_RELATES]:
        "RELATES int_rel" 
        "RELATES F_rel" 
        "RELATES (Id :: (('a \<rightharpoonup> bool)\<times>_)set)"
        by (auto simp: RELATES_def)

      let "?add_idxs prf'" = "set (map snd (filter (Not o fst) prf'))"

      show ?thesis
        unfolding verify2_def verify_def 
        supply [[goals_limit = 1]]
        apply (refine_vcg 
          bind_refine'
          ps_cases2_refine prod_case_refine
          nfoldli_invar_refine[where I="\<lambda>l1 l2 (_,Fx,A). 
              distinct (filter (Not o fst) (l1@l2)) 
              \<and> Fx \<subseteq> set F' \<union> ?add_idxs l1"]
          leof_True_rule[where m="has_rup_or_rat2 _ _ _"]
          leof_True_rule[where m="prop_unit_spec2 _ _"]
          leof_True_rule[where m="has_conflict_spec2 _ _"]
          add_clause2_set_aux
        )
        apply refine_dref_type
        apply (vc_solve split del: split_if solve: asm_rl[of "_\<in>set F'"])
        subgoal using load_clauses2_set_aux[of F'] by (auto simp: pw_leof_iff)
        subgoal unfolding delete_clause2_def apply refine_vcg by auto
        subgoal using PF_DJ by auto 
        done
    qed    

  end


section \<open>Abstraction 3 (Two Watched Literals)\<close>

  context abs_clause_db_defs begin
    definition "watched W i \<equiv> {fst (the (W i)), snd (the (W i))}"

    lemma watched_upd_other[simp]:
      assumes "i'\<noteq>i"
      shows "watched (W(i'\<mapsto>x)) i = watched W i"
      using assms unfolding watched_def by auto

    lemma watched_upd_same[simp]:
      "watched (W(i\<mapsto>x)) i = {fst x, snd x}"
      unfolding watched_def by auto

    lemma watched_upd_conv: "watched (W(i'\<mapsto>x)) i = (if i=i' then {fst x, snd x} else watched W i)"  
      by auto


    definition "prop_unit2_R \<equiv> {((W,A,P),(W',A',P')). 
        finite (dom W) \<and> finite P
      \<and> dom W' = dom W 
      \<and> ((A,A')\<in>(prop_unit_R (CL`dom W))\<^sup>+ 
        \<or> A'=A \<and> P' \<subset> P ) }"  

    lemma prop_unit2_RI: 
      "\<lbrakk> finite (dom W); finite P; dom W' = dom W; (A,A')\<in>(prop_unit_R (CL`dom W))\<^sup>+ \<rbrakk> \<Longrightarrow> ((W,A,P),(W',A',P')) \<in> prop_unit2_R"
      "\<lbrakk> finite (dom W); finite P; dom W' = dom W; A'=A; P' \<subset> P \<rbrakk> \<Longrightarrow> ((W,A,P),(W',A',P')) \<in> prop_unit2_R"
      unfolding prop_unit2_R_def by auto

    lemma prop_unit2_append_unit:
      assumes "((W,A,P),(W',A',P'))\<in>prop_unit2_R"
      assumes "(A',A'')\<in>prop_unit_R (CL`dom W')"
      shows "((W,A,P),(W',A'',P''))\<in>prop_unit2_R"
      using assms
      unfolding prop_unit2_R_def
      by (auto dest: trancl_into_trancl)


    context begin  
      private definition "prop_unit_R' \<equiv> same_fst finite (\<lambda>F. (prop_unit_R F)\<inverse>)"
      private lemma wf_prop_unit_R': "wf prop_unit_R'" unfolding prop_unit_R'_def
        apply (rule wf_same_fst) 
        by (rule wf_prop_unit_R)
  
  
      lemma wf_prop_unit2_R[simp,intro!]: "wf (prop_unit2_R\<inverse>)"  
      proof (rule wf_subset)
        show "prop_unit2_R\<inverse> \<subseteq> inv_image ((prop_unit_R')\<^sup>+ <*lex*> finite_psubset) (\<lambda>(W,A,P). ((CL`dom W, A),P))"
          (is "_ \<subseteq> ?U")
          unfolding prop_unit2_R_def prop_unit_R'_def
          by (auto simp: trancl_converse)
    
        show "wf ?U" using wf_prop_unit_R'[THEN wf_trancl] by auto
      qed  
    end

  end



  locale twl_invar_defs = abs_clause_db_defs DB for DB :: "'idx \<rightharpoonup> 'a clause" +
    fixes W :: "'idx \<rightharpoonup> 'a literal \<times> 'a literal"
    fixes A :: "'a \<rightharpoonup> bool"
    fixes P :: "'a literal set"
    fixes CN :: bool
    fixes it :: "'idx set"
  begin
    abbreviation "F \<equiv> dom W"
    definition "is_covered i \<equiv> watched W i \<inter> P \<noteq> {}"

    lemma in_F_I[simp, intro]: "W i = Some x \<Longrightarrow> i\<in>F" by auto

  end  

  context abs_clause_db_defs begin
  
    lemma covered_upd_other[simp]:
      assumes "i'\<noteq>i"
      shows "twl_invar_defs.is_covered (W(i'\<mapsto>x)) P i = twl_invar_defs.is_covered W P i"
      using assms unfolding twl_invar_defs.is_covered_def by auto
  
    lemma covered_upd_same[simp]:   
      "twl_invar_defs.is_covered (W(i\<mapsto>x)) P i \<longleftrightarrow> fst x \<in> P \<or> snd x \<in> P"
      unfolding twl_invar_defs.is_covered_def by auto
  
    lemma covered_ins_conv:
      "twl_invar_defs.is_covered W (insert l P) i \<longleftrightarrow> 
        twl_invar_defs.is_covered W P i \<or> l\<in>watched W i"
      unfolding twl_invar_defs.is_covered_def  
      by auto
  end    


  locale twl_invar = abs_clause_db DB + twl_invar_defs DB W A P CN it for DB :: "'idx \<rightharpoonup> 'a clause" and W A P CN it +
    assumes W_valid: "dom W \<subseteq> dom DB"
    assumes it_valid: "it \<subseteq> F"
    assumes W_dist_mem: "\<And>w1 w2 i. W i = Some (w1,w2) \<Longrightarrow> w1\<noteq>w2 \<and> w1\<in>CL i \<and> w2\<in>CL i"
    assumes cn_imp_conflict: "CN \<Longrightarrow> \<exists>i\<in>F. is_conflict_clause A (CL i)"
    assumes conflict_covered: "\<lbrakk>i\<in>F - it; \<not>CN; is_conflict_clause A (CL i)\<rbrakk> \<Longrightarrow> is_covered i"
    assumes unit_covered: "\<lbrakk>i\<in>F - it; \<not>CN; is_unit_clause A (CL i)\<rbrakk> \<Longrightarrow> is_covered i"

    assumes finite_P[simp, intro!]: "finite P"
    assumes pending_false: "l\<in>P \<Longrightarrow> sem_lit' l A = Some False"

    assumes watched_invar: "\<And>w1 w2 i. \<lbrakk> \<not>CN; W i = Some (w1,w2); i\<notin>it; sem_lit' w1 A \<noteq> Some True; sem_lit' w2 A \<noteq> Some True \<rbrakk> 
      \<Longrightarrow> (sem_lit' w1 A = Some False \<longrightarrow> w1\<in>P) \<and> (sem_lit' w2 A = Some False \<longrightarrow> w2\<in>P)"
  begin
    lemmas [l_asm_rules] = W_valid it_valid W_dist_mem cn_imp_conflict conflict_covered unit_covered 
      pending_false watched_invar finite_P

    lemma finite_F[simp, intro!]: "finite F"
      using finite_subset[OF W_valid] by auto

    lemma finite_it[simp, intro!]: "finite it"
      using finite_subset[OF it_valid] by auto

    lemma W_mem: 
      assumes "W i = Some (w1,w2)" 
      shows "w1\<in>CL i" and "w2\<in>CL i"
      using W_dist_mem assms by auto

    lemma W_dist: 
      assumes "W i = Some (w1,w2)" 
      shows "w1\<noteq>w2"
      using W_dist_mem assms by auto


  end


  (* TODO: Move *)
  lemma is_covered_empty_iff[simp, intro]: "\<not>twl_invar_defs.is_covered W {} i"
    unfolding twl_invar_defs.is_covered_def by auto

  locale twl_invar_ni = twl_invar DB W A P CN "{}" for DB :: "'idx \<rightharpoonup> 'a clause" and W A P CN

  locale twl_invar_conp = twl_invar_ni DB W A P CN for DB :: "'idx \<rightharpoonup> 'a clause" and W A P CN +
    assumes conflict_or_no_pending: "CN \<or> P={}"
  begin
    lemmas [l_asm_rules] = conflict_or_no_pending
    lemma no_conf_no_pending: "\<not>CN \<Longrightarrow> P={}" using conflict_or_no_pending by auto

    lemma cn_precise: "CN \<longleftrightarrow> (\<exists>i\<in>F. is_conflict_clause A (CL i))"
      using cn_imp_conflict no_conf_no_pending conflict_covered
      by auto

  end  

  locale twl_invar_no_conf = twl_invar_conp DB W A "{}" False for DB :: "'idx \<rightharpoonup> 'a clause" and W A

  locale twl_bt_invar_aux = 
      twl_invar_defs DB W A P CN it
    + IB: twl_invar_no_conf DB W\<^sub>b "A\<^sub>b"
    + twl_invar DB W A P CN it
    for DB :: "'idx \<rightharpoonup> 'a clause" and W\<^sub>b A\<^sub>b W A P CN it TR + 
    assumes AB_EQ: "A\<^sub>b = A |` (-TR)"
    assumes FB_EQ: "IB.F = F"
    assumes new_watched_nf: "\<lbrakk> i\<in>F; w\<in>watched W i - watched W\<^sub>b i \<rbrakk> \<Longrightarrow> sem_lit' w A\<^sub>b \<noteq> Some False"
    assumes watched_keep_true: "\<lbrakk> i\<in>F; w\<in>watched W\<^sub>b i - watched W i \<rbrakk> \<Longrightarrow> sem_lit' w A\<^sub>b \<noteq> Some True"
  begin
    lemmas [l_asm_rules] = AB_EQ FB_EQ new_watched_nf watched_keep_true

    lemma AB_submap: "A\<^sub>b \<subseteq>\<^sub>m A" using AB_EQ by (auto simp: map_le_def)

    lemma A_compat_A\<^sub>b: "A\<^sub>b x = Some v \<Longrightarrow> A x = Some v"
      using AB_submap by (rule map_leD)

    lemma sem_lit_compat\<^sub>b: "sem_lit' l A\<^sub>b = Some v \<Longrightarrow> sem_lit' l A = Some v"  
      using A_compat_A\<^sub>b by (cases l) auto

  end
    
  locale twl_bt_invar = twl_bt_invar_aux where it="{}"

  locale twl_bt_invar_conp = twl_bt_invar + twl_invar_conp


  locale twl_pu_loop_invar = 
    twl_bt_invar_aux DB W\<^sub>b A\<^sub>b W A P CN it TR +
    I0: twl_bt_invar DB W\<^sub>b A\<^sub>b W\<^sub>0 A\<^sub>0 P\<^sub>0 False TR\<^sub>0
    for DB :: "'idx \<rightharpoonup> 'a clause" and W\<^sub>b A\<^sub>b W A P CN it TR W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 l_rem+
    assumes watched_unproc_eq: "i\<in>it \<Longrightarrow> W\<^sub>0 i = W i"
    assumes new_ass_pending: "A x \<noteq> A\<^sub>0 x \<Longrightarrow> A\<^sub>0 x = None \<and> x\<in>var_of_lit`P"
    assumes pending_mono: "P\<^sub>0 - {l_rem} \<subseteq> P"
    assumes l_rem_mem[simp, intro!]: "l_rem \<in> P\<^sub>0"
    assumes pu_rel: "((W\<^sub>0,A\<^sub>0,P\<^sub>0),(W,A,P))\<in>prop_unit2_R"
  begin
    lemmas [l_asm_rules] = watched_unproc_eq new_ass_pending pending_mono l_rem_mem pu_rel

    lemma I0F_EQ: "I0.F = F" using FB_EQ I0.FB_EQ by auto

    lemma A_compat_A\<^sub>0: "A\<^sub>0 x = Some v \<Longrightarrow> A x = Some v"
      using new_ass_pending[of x] by auto

    lemma sem_lit_compat\<^sub>0: "sem_lit' l A\<^sub>0 = Some v \<Longrightarrow> sem_lit' l A = Some v"  
      using A_compat_A\<^sub>0 by (cases l) auto
      
    lemma new_sem_pendingE[consumes 1, case_names unchanged pending]: 
      assumes "sem_lit' l A = Some False"  
      obtains "sem_lit' l A\<^sub>0 = Some False" | "sem_lit' l A\<^sub>0 = None" "l\<in>P"
    proof (cases "sem_lit' l A\<^sub>0")  
      case false with that show thesis by blast
    next
      case true with assms sem_lit_compat\<^sub>0[of l] have False by auto
      thus thesis ..
    next  
      case undec 
      with assms new_ass_pending[of "var_of_lit l"] have "var_of_lit l \<in> var_of_lit`P"
        by (cases l) auto
      hence "l\<in>P \<or> neg_lit l \<in> P" 
        by (metis (no_types, lifting) imageE neg_lit.simps(2) neg_neg_lit var_of_lit.elims)
      with pending_false assms have "l\<in>P" by fastforce
      with undec that show thesis by auto
    qed
  end  
    

  context  
    fixes DB :: "'idx \<rightharpoonup> 'a clause"
    fixes W\<^sub>b :: "'idx \<rightharpoonup> 'a literal \<times> 'a literal"
    fixes A\<^sub>b :: "'a \<rightharpoonup> bool"
  begin

    interpretation abs_clause_db_defs DB .


    definition "twl_prop_unit_step W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 \<equiv> do {

      ASSERT (twl_bt_invar DB W\<^sub>b A\<^sub>b W\<^sub>0 A\<^sub>0 P\<^sub>0 False TR\<^sub>0);

      l_rem \<leftarrow> OBTAIN (\<lambda>l. l\<in>P\<^sub>0);
      let P = P\<^sub>0 - {l_rem};
      

      let WS = { i\<in>dom W\<^sub>0. l_rem \<in> watched W\<^sub>0 i};

      (W,A,P,TR,CN) \<leftarrow> FOREACHci 
        (\<lambda>it (W,A,P,TR,CN). twl_pu_loop_invar DB W\<^sub>b A\<^sub>b W A P CN it TR W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 l_rem)
        WS (\<lambda>(W,A,P,TR,CN). \<not>CN) (\<lambda>i (W,A,P,TR,_). do {
        let (w1,w2) = the (W i);
        if (sem_lit' w1 A = Some True \<or> sem_lit' w2 A = Some True) then
          RETURN (W,A,P,TR,False)
        else do {  
          let (w1,w2) = (if w1=l_rem then (w2,w1) else (w1,w2));
          ASSERT (w2=l_rem);
          ASSERT (w1\<noteq>w2);
  
          w' \<leftarrow> SELECT (\<lambda>w'. w'\<noteq>w1 \<and> w'\<in>CL i \<and> sem_lit' w' A \<noteq> Some False);
          case w' of 
            Some w' \<Rightarrow> do { let W = W(i\<mapsto>(w1,w')); RETURN (W,A,P,TR,False) }
          | None \<Rightarrow> do {
              if sem_lit' w1 A = Some False then do {
                ASSERT (is_conflict_clause A (CL i));
                RETURN (W,A,P,TR,True)
              } else do {
                ASSERT (is_unit_lit A (CL i) w1);
                RETURN (W,assign_lit A w1,insert (neg_lit w1) P,insert (var_of_lit w1) TR,False)
              }
            }
        }
      }) (W\<^sub>0,A\<^sub>0,P,TR\<^sub>0,False);

      RETURN (W,A,P,TR,CN)
    }"


    lemma twl_prop_unit_step_correct_aux:
      assumes "twl_bt_invar DB W\<^sub>b A\<^sub>b W\<^sub>0 A\<^sub>0 P\<^sub>0 False TR\<^sub>0"
      assumes "P\<^sub>0\<noteq>{}"
      shows "twl_prop_unit_step W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 \<le> SPEC (\<lambda>(W,A,P,TR,CN). 
        twl_bt_invar DB W\<^sub>b A\<^sub>b W A P CN TR 
        \<and> ((W\<^sub>0,A\<^sub>0,P\<^sub>0),(W,A,P))\<in>prop_unit2_R
      )"
      unfolding twl_prop_unit_step_def
      using assms
      apply refine_vcg
      apply (vc_solve del: notI solve: asm_rl[of "\<exists>x. x\<in>_"])
    proof -  
      assume "twl_bt_invar DB W\<^sub>b A\<^sub>b W\<^sub>0 A\<^sub>0 P\<^sub>0 False TR\<^sub>0"
      then interpret I0: twl_bt_invar DB W\<^sub>b A\<^sub>b W\<^sub>0 A\<^sub>0 P\<^sub>0 False TR\<^sub>0 .
      fix l_rem
      assume L_REM_MEM: "l_rem \<in> P\<^sub>0"

      show "finite {i \<in> I0.F. l_rem \<in> watched W\<^sub>0 i}" by auto
        
      { -- \<open>Enter loop\<close>
        show "twl_pu_loop_invar DB W\<^sub>b A\<^sub>b W\<^sub>0 A\<^sub>0 (P\<^sub>0 - {l_rem}) False {i \<in> I0.F. l_rem \<in> watched W\<^sub>0 i}
                  TR\<^sub>0 W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 l_rem"
          apply (unfold_locales; try_lasms)
          using I0.W_valid "I0.W_dist_mem" I0.AB_EQ I0.FB_EQ "I0.new_watched_nf" "I0.watched_keep_true"
          apply (vc_solve simp: I0.pending_false L_REM_MEM del: notI)
          subgoal for i w1 w2 using I0.conflict_covered[of i]
            by (auto simp: "twl_invar_defs.is_covered_def")
          subgoal for i w1 w2 using I0.unit_covered[of i]
            by (auto simp: "twl_invar_defs.is_covered_def")
          subgoal for w1 w2 i using I0.watched_invar[of i w1 w2]   
            by (auto simp: watched_def)
          subgoal 
            apply (rule prop_unit2_RI(2))  
            using L_REM_MEM
            by auto
            
          done

        { -- \<open>Inside loop\<close>
          fix W A P it TR
          assume "twl_pu_loop_invar DB W\<^sub>b A\<^sub>b W A P False it TR W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 l_rem"
          then interpret twl_pu_loop_invar DB W\<^sub>b A\<^sub>b W A P False it TR W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 l_rem .


          from I0.pending_false[OF L_REM_MEM] sem_lit_compat\<^sub>0 
          have SLLREM: "sem_lit' l_rem A = Some False" by auto

          assume IT_SS: "it \<subseteq> {i \<in> I0.F. l_rem \<in> watched W\<^sub>0 i}"
          
          fix i w1 w2
          assume II: "i \<in> it" and "the (W i) = (w1,w2)"
          with it_valid have Wi: "W i = Some (w1,w2)" by auto
          from II it_valid have [simp, intro!]: "i\<in>F" by auto

          (*note [simp] = W_dist[OF Wi]*)

          { -- \<open>One watched literal was true\<close> 
            assume ONE_TRUE: "sem_lit' w1 A = Some True \<or> sem_lit' w2 A = Some True"

            hence [simp]: "sem_clause' (CL i) A = Some True" 
              using W_mem[OF Wi]
              by (auto simp: sem_clause'_true_conv)

            hence [simp]: "\<not>is_unit_clause A (CL i)"
              using unit_clause_sem by force

            show "twl_pu_loop_invar DB W\<^sub>b A\<^sub>b W A P False (it - {i}) TR W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 l_rem"
              apply (unfold_locales; try_lasms)
              subgoal using it_valid by auto []
              subgoal for w1' w2' j using watched_invar[of j w1' w2'] ONE_TRUE Wi
                by auto
              done
          }  

          assume NONE_TRUE: "sem_lit' w1 A \<noteq> Some True" "sem_lit' w2 A \<noteq> Some True"
          { -- \<open>Swap literals\<close>
            fix w1' w2'
            assume SWAP_ASS: "(if w1=l_rem then (w2,w1) else (w1,w2)) = (w1',w2')"
            thus [simp]: "w2'=l_rem"
              using Wi IT_SS watched_unproc_eq II
              by (auto split: split_if_asm simp: watched_def)
            
            from SWAP_ASS W_dist[OF Wi] show Wi'_NEQ: "w1'\<noteq>l_rem" 
              by (auto split: split_if_asm)

            from SWAP_ASS W_mem[OF Wi] have W1'_IN_CL[simp, intro!]: "w1'\<in>CL i" by (auto split: split_if_asm)

            from SWAP_ASS Wi have [simp]: "watched W i = {w1',l_rem}"
              by (auto simp: watched_def split: split_if_asm)

            from SWAP_ASS NONE_TRUE have NONE_TRUE': "sem_lit' w1' A \<noteq> Some True"
              by (auto split: split_if_asm)

            txt \<open>If other watched literal is false, it must be covered\<close>  
            have WF_PENDING: "w1'\<in>P" if "sem_lit' w1' A = Some False" 
              using that
            proof (cases rule: new_sem_pendingE)
              case pending thus ?thesis by simp
            next
              case unchanged
              from L_REM_MEM I0.pending_false have "sem_lit' l_rem A\<^sub>0 = Some False" by auto
              with unchanged I0.watched_invar[of i w1 w2] watched_unproc_eq[OF II] Wi SWAP_ASS have "w1'\<in>P\<^sub>0"
                by (auto split: split_if_asm)
              with pending_mono Wi'_NEQ show "w1'\<in>P" by auto
            qed

            { -- \<open>Selected new watched literal\<close>
              fix w'
              assume W'_NEQ: "w'\<noteq>w1'" and W'_IN_CL: "w'\<in>CL i" and SLW': "sem_lit' w' A \<noteq> Some False"

              from SLW' sem_lit_compat\<^sub>b have SLW'b: "sem_lit' w' A\<^sub>b \<noteq> Some False"
                by auto

              from SLLREM SLW' have W'NLR: "w'\<noteq>l_rem" by auto

              from W'_IN_CL SLW' have [simp]: "sem_clause' (CL i) A \<noteq> Some False"
                by (auto simp: sem_clause'_false_conv)

              
              txt \<open>If clause is unit-clause, the other watched literal must be covered\<close>  
              {
                assume "is_unit_clause A (CL i)"
                with sem_not_false_the_unit_lit[OF _ W'_IN_CL SLW'] have "is_unit_lit A (CL i) w'"
                  by (auto simp: is_unit_clause_def)
                from unit_other_false[OF this W1'_IN_CL W'_NEQ] have "sem_lit' w1' A = Some False" .
                hence "w1' \<in> P" by (rule WF_PENDING)
              } note UNIT_COVERED = this

              show "twl_pu_loop_invar DB W\<^sub>b A\<^sub>b (W(i \<mapsto> (w1', w'))) A P False (it - {i}) TR W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 l_rem"
                apply (unfold_locales; try_lasms)
                subgoal using II it_valid W_valid by auto
                subgoal using it_valid by auto
                subgoal for w1j w2j j using W_dist_mem[of j w1j w2j]
                  SWAP_ASS W'_NEQ W_mem[OF Wi] W'_IN_CL
                  by (auto split: split_if_asm)
                subgoal for i'
                  using conflict_covered II covered_upd_other[of i i' W "(w1',w')" P] 
                  by (auto simp del: covered_upd_other)
                subgoal for i'
                  using unit_covered II covered_upd_other[of i i' W "(w1',w')" P] 
                  by (auto simp del: covered_upd_other simp: UNIT_COVERED)
                subgoal using watched_invar SLW' WF_PENDING by (auto split: split_if_asm)
                subgoal using FB_EQ Wi by auto
                subgoal for i' ww using new_watched_nf[of i' ww] SLW'b
                  by (auto simp: watched_upd_conv split: split_if_asm)
                subgoal for i' ww using watched_keep_true[of i' ww] SLLREM 
                  sem_lit_compat\<^sub>b[of ww True]
                  apply (clarsimp simp: watched_upd_conv split: split_if_asm)
                  apply fastforce
                  done
                subgoal using watched_unproc_eq by auto
                subgoal using pu_rel unfolding prop_unit2_R_def by auto
                done
            }  

            { -- \<open>All literals except other watched one are false\<close>
              assume OTHERS_FALSE: "\<forall>l. l\<in>CL i \<longrightarrow> l=w1' \<or> sem_lit' l A = Some False"

              { -- \<open>The other watched literal is also false\<close>
                assume "sem_lit' w1' A = Some False"
                thus CNC: "is_conflict_clause A (CL i)" using OTHERS_FALSE
                  by (auto simp: sem_clause'_false_conv)

                show "twl_pu_loop_invar DB W\<^sub>b A\<^sub>b W A P True (it - {i}) TR W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 l_rem"  
                  apply (unfold_locales; try_lasms)
                  subgoal using it_valid by auto
                  subgoal using CNC by auto
                  done
              }
              { -- \<open>The other watched literal is undecided\<close>
                assume "sem_lit' w1' A \<noteq> Some False"
                hence SLW1': "sem_lit' w1' A = None" using NONE_TRUE' by (cases "sem_lit' w1' A") auto
                thus "is_unit_lit A (CL i) w1'" using OTHERS_FALSE
                  by (auto simp: is_unit_lit_def sem_clause'_false_conv)
                hence [simp]: "sem_clause' (CL i) A = None" by (rule unit_clause_sem') 
                
                let ?A' = "assign_lit A w1'"

                from SLW1' pending_false have [simp, intro!]: "w1'\<notin>P" by auto

                { -- \<open>If some other uncovered clause contains other literal,
                    it is not a unit/conflict clause\<close>
                  fix i' ww1 ww2
                  assume 
                    A: "W i'=Some (ww1,ww2)" "i'\<notin>it" 
                    and "neg_lit w1' \<in> CL i'" 
                    and NCOV: "\<not>twl_invar_defs.is_covered W (insert (neg_lit w1') P) i'"
                  
                  from NCOV A have NEQ: "ww1\<noteq>neg_lit w1'" "ww2\<noteq>neg_lit w1'" and NCOV': "\<not>is_covered i'"
                    by (auto simp: twl_invar_defs.is_covered_def watched_def)

                  from A W_dist_mem have DIST_MEM: "ww1\<noteq>ww2" "ww1\<in>CL i'" "ww2\<in>CL i'" by auto

                  from A NCOV' have "ww1\<notin>P" "ww2\<notin>P" 
                    by (auto simp: twl_invar_defs.is_covered_def watched_def)
                  with watched_invar[OF _ A] have 
                    "sem_lit' ww1 A = Some True 
                    \<or> sem_lit' ww2 A = Some True 
                    \<or> (sem_lit' ww1 A \<noteq> Some False \<and> sem_lit' ww2 A \<noteq> Some False)" 
                    by auto
                  hence CASES':
                    "sem_lit' ww1 ?A' = Some True 
                    \<or> sem_lit' ww2 ?A' = Some True 
                    \<or> (sem_lit' ww1 ?A' \<noteq> Some False \<and> sem_lit' ww2 ?A' \<noteq> Some False)" 
                    using NEQ
                    by (auto simp: sem_lit'_assign_conv)

                  from CASES' have 1: "\<not>is_conflict_clause ?A' (CL i')" 
                    using DIST_MEM
                    by (fastforce simp: sem_clause'_false_conv)

                  from CASES' have 2: "\<not>is_unit_clause ?A' (CL i')" 
                    using DIST_MEM unit_contains_no_true two_nfalse_not_unit
                    by fastforce

                  note 1 2  
                } note OTHER_CU_AUX = this

                txt \<open>By unit propagation, the original clause becomes true\<close>
                have [simp]: "sem_clause' (CL i) (assign_lit A w1') = Some True"
                  by (force simp: sem_clause'_true_conv)
                from unit_contains_no_true[of "(assign_lit A w1')" "CL i" w1'] 
                have [simp]: "\<not>is_unit_clause (assign_lit A w1') (CL i)" by auto

                show "twl_pu_loop_invar DB W\<^sub>b A\<^sub>b W ?A' (insert (neg_lit w1') P) False (it - {i}) (insert (var_of_lit w1') TR) W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 l_rem"  
                  apply (unfold_locales; try_lasms)
                  subgoal using it_valid by auto
                  subgoal for i'
                    apply (cases "i'=i")
                    subgoal by auto
                    subgoal using OTHER_CU_AUX(1)[of i'] 
                    by (auto elim!: clause_assign_false_cases simp: covered_ins_conv conflict_covered[of i'])
                    done
                  subgoal for i'
                    apply (cases "i'=i")
                    subgoal by auto
                    subgoal using OTHER_CU_AUX(2)[of i'] unit_covered[of i']
                      by (auto elim!: clause_assign_unit_cases simp: covered_ins_conv)
                    done
                  subgoal using pending_false by (auto simp: sem_lit'_assign_conv)  
                  subgoal for ww1 ww2 i'
                    apply (cases "i'=i")
                    subgoal using Wi SWAP_ASS by (auto split: split_if_asm)
                    subgoal using watched_invar[of i' ww1 ww2]
                      by (auto simp: sem_lit'_assign_conv SLW1')
                    done  
                  subgoal using AB_EQ SLW1' 
                    apply (cases w1')
                    by (auto intro!: ext simp: restrict_map_def)
                  subgoal for x using new_ass_pending[of x] SLW1'
                    apply (cases w1')
                    apply (auto simp: assign_lit_def split: split_if_asm intro: ccontr) 
                    done
                  subgoal using pending_mono by auto
                  subgoal 
                    apply (rule prop_unit2_append_unit[OF pu_rel]) 
                    apply (rule prop_unit_R.step[of "CL i"])
                    apply simp apply fact
                    done
                  done
              }
            }
          }

        }  
      }

      { -- \<open>Exit loop normally\<close>
        fix W A P TR
        assume "twl_pu_loop_invar DB W\<^sub>b A\<^sub>b W A P False {} TR W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 l_rem"
        then interpret twl_pu_loop_invar DB W\<^sub>b A\<^sub>b W A P False "{}" TR W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 l_rem .
        show "twl_bt_invar DB W\<^sub>b A\<^sub>b W A P False TR"
          by unfold_locales

        from pu_rel show "((W\<^sub>0, A\<^sub>0, P\<^sub>0), W, A, P) \<in> prop_unit2_R" . 
      }

      { -- \<open>Interrupt loop\<close>
        fix W A P TR it
        assume "twl_pu_loop_invar DB W\<^sub>b A\<^sub>b W A P True it TR W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 l_rem"
        and "it \<subseteq> {i \<in> I0.F. l_rem \<in> watched W\<^sub>0 i}"

        interpret twl_pu_loop_invar DB W\<^sub>b A\<^sub>b W A P True it TR W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 l_rem by fact

        show "twl_bt_invar DB W\<^sub>b A\<^sub>b W A P True TR"
          by (unfold_locales; try_lasms)

        from pu_rel show "((W\<^sub>0, A\<^sub>0, P\<^sub>0), W, A, P) \<in> prop_unit2_R" . 
      }
    qed

    text \<open>Get rid of ghost variables\<close>
    schematic_goal twl_prop_unit_step'_aux: "?c \<le> twl_prop_unit_step W A P TR"
      unfolding twl_prop_unit_step_def
      supply ASSERT_removeg[where \<Phi>="twl_bt_invar _ _ _ _ _ _ _ _",remove_ghost_rules]
      supply FOREACHci_removeg[remove_ghost_rules]
      by (tactic \<open>remove_ghost_tac @{context} 1\<close>)

    concrete_definition twl_prop_unit_step' for W A P TR uses twl_prop_unit_step'_aux is "?pat \<le> _"

    lemmas twl_prop_unit_step'_correct[THEN order_trans, refine_vcg] = 
      order_trans[OF twl_prop_unit_step'.refine twl_prop_unit_step_correct_aux]


    definition "twl_prop_unit W A P TR \<equiv> 
      WHILET (\<lambda>(W,A,P,TR,CN). \<not>CN \<and> P\<noteq>{}) (\<lambda>(W,A,P,TR,CN). do {
        twl_prop_unit_step' W A P TR
      }) (W,A,P,TR,False)"

    lemma twl2_prop_unit_correct_aux: 
      assumes A: "twl_bt_invar DB W\<^sub>b A\<^sub>b W\<^sub>0 A\<^sub>0 P\<^sub>0 False TR\<^sub>0"  
      shows "twl_prop_unit W\<^sub>0 A\<^sub>0 P\<^sub>0 TR\<^sub>0 \<le> SPEC (\<lambda>(W,A,P,TR,CN). 
        twl_bt_invar_conp DB W\<^sub>b A\<^sub>b W A P CN TR 
        \<and> ((W\<^sub>0,A\<^sub>0,P\<^sub>0),(W,A,P))\<in>prop_unit2_R\<^sup>*)"
      unfolding twl_prop_unit_def  
      apply (refine_vcg WHILET_rule[where 
          I="\<lambda>(W,A,P,TR,CN). twl_bt_invar DB W\<^sub>b A\<^sub>b W A P CN TR \<and> ((W\<^sub>0,A\<^sub>0,P\<^sub>0),(W,A,P))\<in>prop_unit2_R\<^sup>*" and
          R="inv_image (prop_unit2_R\<inverse>) (\<lambda>(W,A,P,TR,CN). (W,A,P))"]
      )
      apply (vc_solve simp: A)
      subgoal by (blast intro: rtrancl_into_rtrancl)
      subgoal premises prems for W A P TR CN proof -
        from prems interpret twl_bt_invar DB W\<^sub>b A\<^sub>b W A P CN TR by simp
        from prems show "twl_bt_invar_conp DB W\<^sub>b A\<^sub>b W A P CN TR"
          by unfold_locales
      qed
      done

  end

  context twl_bt_invar begin  
    lemma ncap_no_unit:
      assumes [simp]: "P={}" "\<not>CN"
      shows "\<not>(\<exists>i\<in>F. is_unit_clause A (CL i))"
      using unit_covered unfolding is_covered_def by auto

    lemma np_cn_precise:
      assumes [simp]: "P={}"
      shows "CN \<longleftrightarrow> (\<exists>i\<in>F. is_conflict_clause A (CL i))"
      using conflict_covered cn_imp_conflict unfolding is_covered_def by auto

  end

  context twl_bt_invar_conp begin
    lemma cn_precise: "CN \<longleftrightarrow> (\<exists>i\<in>F. is_conflict_clause A (CL i))"
      using conflict_or_no_pending np_cn_precise cn_imp_conflict by auto

    lemma nc_no_unit: "\<not>CN \<Longrightarrow> \<not>(\<exists>i\<in>F. is_unit_clause A (CL i))"
      using conflict_or_no_pending ncap_no_unit by auto

  end



  context abs_clause_db begin
    term twl_prop_unit

    definition "twl_A_\<alpha> \<equiv> (\<lambda>(W, A, P, _). A)"
    definition "twlR_bt_invar A\<^sub>b F \<equiv> \<lambda>(W, A, P, TR). F=dom W \<and> (\<exists>W\<^sub>b. twl_bt_invar DB W\<^sub>b A\<^sub>b W A P False TR)"
    definition "twlR_bt_invar_conp A\<^sub>b F \<equiv> \<lambda>(W, A, P, TR, CN). F=dom W \<and> (\<exists>W\<^sub>b. twl_bt_invar_conp DB W\<^sub>b A\<^sub>b W A P CN TR)"

    lemma prop_unit2_R_tranclD:
      assumes "((W,A,P),(W',A',P'))\<in> prop_unit2_R\<^sup>*"
      shows "dom W' = dom W \<and> (A,A')\<in>(prop_unit_R (CL`dom W))\<^sup>*"
      using assms
      apply (induction rule: rtrancl_induct[where a="(W,A,P)" for W A P, split_format (complete)])
      apply (auto simp: prop_unit2_R_def)
      done

    lemma twl_prop_unit_refine[refine]:
      assumes "((W,Ai,P,TR),A) \<in> br twl_A_\<alpha> (twlR_bt_invar A\<^sub>b F)"
      shows "twl_prop_unit DB W Ai P TR \<le> \<Down>(br twl_A_\<alpha> (twlR_bt_invar_conp A\<^sub>b F)) (prop_unit_spec2 F A)"
      using assms unfolding in_br_conv twlR_bt_invar_def
      apply clarsimp
      unfolding prop_unit_spec2_def
      apply (refine_vcg SPEC_refine twl2_prop_unit_correct_aux[THEN order_trans])
      apply assumption
      apply (vc_solve simp: in_br_conv twlR_bt_invar_conp_def twl_A_\<alpha>_def dest!: prop_unit2_R_tranclD)
      apply (intro conjI; (auto;fail)?)
      subgoal premises prems for W\<^sub>b W' A P TR CN proof -
        from prems interpret twl_bt_invar_conp DB W\<^sub>b A\<^sub>b W' A P CN TR by simp
        from prems have [simp]: "dom W = dom W'" by simp
        show "(\<forall>x\<in>dom W. \<not> is_unit_clause A (CL x)) \<or> (\<exists>i\<in>dom W. sem_clause' (CL i) A = Some False)"
          using cn_precise nc_no_unit by auto
      qed  
      done


  end

  text \<open>We project out the trail, such we also obtain a unit-propagation procedure without a trail.
    The correctness of this procedure is proved from the original refinement lemma, and the fact that
    we can always obtain some dummy backtrack point.\<close>

  lemma (in twl_invar_ni) init_backtrack_dummy:
    "twl_bt_invar DB W Map.empty W A P CN (dom A)"
    apply (unfold_locales; try_lasms)
    subgoal for i
      using W_mem[of i]
      by (auto simp: sem_clause'_false_conv)
    subgoal for i  
      using W_mem[of i]
      apply (clarsimp simp: sem_clause'_false_conv is_unit_clause_def is_unit_lit_def)
      using W_dist
      apply force
      done
    done  


  context abs_clause_db 
  begin
    definition "twl_prop_unit_step_ntr W\<^sub>0 A\<^sub>0 P\<^sub>0 \<equiv> do {

      l_rem \<leftarrow> OBTAIN (\<lambda>l. l\<in>P\<^sub>0);
      let P = P\<^sub>0 - {l_rem};
      

      let WS = { i\<in>dom W\<^sub>0. l_rem \<in> watched W\<^sub>0 i};

      (W,A,P,CN) \<leftarrow> FOREACHc 
        WS (\<lambda>(W,A,P,CN). \<not>CN) (\<lambda>i (W,A,P,_). do {
        let (w1,w2) = the (W i);
        if (sem_lit' w1 A = Some True \<or> sem_lit' w2 A = Some True) then
          RETURN (W,A,P,False)
        else do {  
          let (w1,w2) = (if w1=l_rem then (w2,w1) else (w1,w2));
          ASSERT (w2=l_rem);
          ASSERT (w1\<noteq>w2);
  
          w' \<leftarrow> SELECT (\<lambda>w'. w'\<noteq>w1 \<and> w'\<in>CL i \<and> sem_lit' w' A \<noteq> Some False);
          case w' of 
            Some w' \<Rightarrow> do { let W = W(i\<mapsto>(w1,w')); RETURN (W,A,P,False) }
          | None \<Rightarrow> do {
              if sem_lit' w1 A = Some False then do {
                ASSERT (is_conflict_clause A (CL i));
                RETURN (W,A,P,True)
              } else do {
                ASSERT (is_unit_lit A (CL i) w1);
                RETURN (W,assign_lit A w1,insert (neg_lit w1) P,False)
              }
            }
        }
      }) (W\<^sub>0,A\<^sub>0,P,False);

      RETURN (W,A,P,CN)
    }"

    definition "notr_rel \<equiv> {((W,A,P,CN),(W,A,P,TR,CN)) | W A P TR CN. True}"

    lemma twl_prop_unit_step_ntr_refine: 
      assumes [simplified,simp]: "(Wi,W)\<in>Id" "(Ai,A)\<in>Id" "(Pi,P)\<in>Id"
      shows "twl_prop_unit_step_ntr Wi Ai Pi \<le>\<Down>notr_rel (twl_prop_unit_step' DB W A P TR)"
    proof -
      have [refine_dref_RELATES]: "RELATES notr_rel" by (simp add: RELATES_def)

      show ?thesis
        unfolding twl_prop_unit_step_ntr_def twl_prop_unit_step'_def
        supply [[goals_limit = 1]]
        apply (refine_rcg inj_on_id)
        apply refine_dref_type
        apply (auto simp: notr_rel_def split: split_if_asm)
        done
    qed

    definition "twl_prop_unit_ntr W A P \<equiv> 
      WHILET (\<lambda>(W,A,P,CN). \<not>CN \<and> P\<noteq>{}) (\<lambda>(W,A,P,CN). do {
        twl_prop_unit_step_ntr W A P
      }) (W,A,P,False)"

    lemma twl_prop_unit_ntr_refine_aux: 
      assumes [simplified,simp]: "(Wi,W)\<in>Id" "(Ai,A)\<in>Id" "(Pi,P)\<in>Id"
      shows "twl_prop_unit_ntr Wi Ai Pi \<le>\<Down>notr_rel (twl_prop_unit DB W A P TR)"
        unfolding twl_prop_unit_ntr_def twl_prop_unit_def
        apply (refine_rcg twl_prop_unit_step_ntr_refine)
        apply (auto simp: notr_rel_def)
        done
      
    definition "WAP_rel \<equiv> br 
      (\<lambda>(W,A,P). (dom W,A)) 
      (\<lambda>(W,A,P). twl_invar_ni DB W A P False)"

    definition "WAPC_rel \<equiv> br 
      (\<lambda>(W,A,P,CN). (dom W,A)) 
      (\<lambda>(W,A,P,CN). twl_invar_ni DB W A P CN)"

    definition "WAPC_relA F \<equiv> br 
      (\<lambda>(W,A,P,CN). A) 
      (\<lambda>(W,A,P,CN). F = dom W \<and> twl_invar_ni DB W A P CN)"

    definition "WAPC_relA_conp F \<equiv> br 
      (\<lambda>(W,A,P,CN). A) 
      (\<lambda>(W,A,P,CN). F = dom W \<and> twl_invar_conp DB W A P CN)"

    lemma twl_prop_unit_ntr_refine[refine]:
      assumes "((W,Ai,P),(F,A)) \<in> WAP_rel"
      shows "twl_prop_unit_ntr W Ai P \<le> \<Down>(WAPC_relA_conp F) (prop_unit_spec2 F A)"
    proof -
      from assms have [simp]: "F = dom W" "Ai=A" and
        "twl_invar_ni DB W A P False"
        by (auto simp: WAP_rel_def in_br_conv)
      interpret twl_invar_ni DB W A P False by fact  

      have 1: "((W, A, P, dom A), A) \<in> br twl_A_\<alpha> (twlR_bt_invar Map.empty (dom W))"
        using init_backtrack_dummy
        by (auto simp: br_def twl_A_\<alpha>_def twlR_bt_invar_def)

      note twl_prop_unit_ntr_refine_aux[OF IdI IdI IdI, of W A P "dom A"]
      also note twl_prop_unit_refine[of W A P "dom A" A Map.empty "dom W"]
      finally have 
        2: "twl_prop_unit_ntr W A P \<le> \<Down> (notr_rel O br twl_A_\<alpha> (twlR_bt_invar_conp Map.empty (dom W))) (prop_unit_spec2 (dom W) A)"
        using 1 by (simp add: conc_fun_chain)

      thm conc_fun_mono[THEN monoD]  

      have 3: "notr_rel O br twl_A_\<alpha> (twlR_bt_invar_conp Map.empty (dom W)) \<subseteq> WAPC_relA_conp F"
        apply (clarsimp simp: notr_rel_def WAPC_relA_conp_def br_def twl_A_\<alpha>_def twlR_bt_invar_conp_def)
      proof -  
        fix W A P TR CN W\<^sub>b
        assume "twl_bt_invar_conp DB W\<^sub>b Map.empty W A P CN TR"
        then interpret I: twl_bt_invar_conp DB W\<^sub>b Map.empty W A P CN TR .
        show "twl_invar_conp DB W A P CN"
          by unfold_locales
      qed    

      show ?thesis 
        apply simp
        apply (rule order_trans[OF 2 conc_fun_R_mono])
        using 3 by simp

    qed    


  end  









  text \<open>Backtracking\<close>

  context twl_bt_invar_aux begin
    text \<open>Reverting the assignment to the backtrack point yields a valid 
      data structure, although watched literals may have changed\<close>

    lemma backtrack: "twl_invar_no_conf DB W A\<^sub>b"
      apply (unfold_locales; try_lasms)
      subgoal 
        using FB_EQ IB.conflict_covered IB.is_covered_def by blast
      subgoal 
        using FB_EQ IB.is_covered_def IB.unit_covered by blast
      subgoal for w1 w2 i
      proof (clarsimp; safe)
        assume 
          Wi: "W i = Some (w1, w2)" 
          and NOT_TRUE: "sem_lit' w1 A\<^sub>b \<noteq> Some True" "sem_lit' w2 A\<^sub>b \<noteq> Some True"

        from Wi have [simp,intro!]: "i\<in>F" by auto

        obtain w1\<^sub>b w2\<^sub>b where Wbi: "W\<^sub>b i = Some (w1\<^sub>b,w2\<^sub>b)" using Wi FB_EQ by fastforce

        from Wi Wbi NOT_TRUE watched_keep_true[of i] have
          NOT_TRUE\<^sub>b: "sem_lit' w1\<^sub>b A\<^sub>b \<noteq> Some True" "sem_lit' w2\<^sub>b A\<^sub>b \<noteq> Some True"
          by (auto simp: watched_def)

        {
          assume F: "sem_lit' w1 A\<^sub>b = Some False"
          {
            assume "w1 = w1\<^sub>b \<or> w1=w2\<^sub>b"
            with IB.watched_invar[OF _ Wbi] F NOT_TRUE\<^sub>b have False by auto
          } moreover {
            assume "w1 \<noteq> w1\<^sub>b \<and> w1\<noteq>w2\<^sub>b"
            hence "w1 \<in> watched W i - watched W\<^sub>b i" using Wi Wbi by (auto simp: watched_def)
            from new_watched_nf[OF \<open>i\<in>F\<close> this] F have False by simp
          } ultimately show False by blast
        }

        {
          assume F: "sem_lit' w2 A\<^sub>b = Some False"
          {
            assume "w2 = w1\<^sub>b \<or> w2=w2\<^sub>b"
            with IB.watched_invar[OF _ Wbi] F NOT_TRUE\<^sub>b have False by auto
          } moreover {
            assume "w2 \<noteq> w1\<^sub>b \<and> w2\<noteq>w2\<^sub>b"
            hence "w2 \<in> watched W i - watched W\<^sub>b i" using Wi Wbi by (auto simp: watched_def)
            from new_watched_nf[OF \<open>i\<in>F\<close> this] F have False by simp
          } ultimately show False by blast
        }
      qed
      done

      lemma backtrack': "twl_invar_no_conf DB W (A |`(-TR))"
        using backtrack AB_EQ by simp


  end


  context twl_invar_no_conf begin
    lemma init_backtrack: "twl_bt_invar DB W A W A {} False {}"
      by (unfold_locales; try_lasms)

  end

  context abs_clause_db begin

    definition "twl_assign_all_negated W A C \<equiv> do {
      let UD = {l\<in>C. sem_lit' l A = None};
      let A = assign_all_negated A C;
      RETURN (W,A,UD,var_of_lit`UD)
    }"

    definition "twl_has_rup W A C \<equiv> do {
      ASSERT (up_no_conflict (CL`dom W) A);
      ASSERT (finite C);
      if \<exists>l\<in>C. sem_lit' l A = Some True \<or> neg_lit l \<in> C then
        RETURN (True,(W,A))
      else do {
        (W,A,P,TR) \<leftarrow> twl_assign_all_negated W A C;
        (W,A,P,TR,CN) \<leftarrow> twl_prop_unit DB W A P TR;
        let A = A |`(-TR);
        RETURN (CN,(W,A))
      }
    }"

    lemma sem_lit_assign_all_negated_cases[consumes 1, case_names None Neg Pos]:
      assumes "sem_lit' l (assign_all_negated A C) = Some v"
      obtains "sem_lit' l A = Some v" 
            | "sem_lit' l A = None" "neg_lit l \<in> C" "v=True"
            | "sem_lit' l A = None" "l \<in> C" "v=False"
      using assms unfolding assign_all_negated_def
      apply (cases l)
      apply (auto simp: map_add_def split: split_if_asm)
      done
      
    lemma sem_lit_assign_all_negated_none_iff:
      "sem_lit' l (assign_all_negated A C) = None \<longleftrightarrow> (sem_lit' l A = None \<and> l\<notin>C \<and> neg_lit l \<notin> C)"  
      using assms unfolding assign_all_negated_def
      apply (cases l)
      apply (auto simp: map_add_def split: split_if_asm)
      done
      
    lemma sem_lit_assign_all_negated_pres_decided:
      assumes "sem_lit' l A = Some v"
      shows "sem_lit' l (assign_all_negated A C) = Some v"
      using assms unfolding assign_all_negated_def
      apply (cases l)
      apply (fastforce simp: map_add_def split: split_if_asm)+
      done

    lemma sem_lit_assign_all_negated_assign: 
      assumes "\<forall>l\<in>C. neg_lit l\<notin>C" "l \<in> C" "sem_lit' l A = None"
      shows "sem_lit' l (assign_all_negated A C) = Some False"  
      using assms unfolding assign_all_negated_def
      apply (cases l)
      apply (auto simp: map_add_def split: split_if_asm)
      done
      
    lemma sem_lit_assign_all_negated_neqv: 
      "sem_lit' l (assign_all_negated A C) \<noteq> Some v \<Longrightarrow> sem_lit' l A \<noteq> Some v"
      by (auto simp: sem_lit_assign_all_negated_pres_decided)

    lemma sem_lit'_none_conv: "sem_lit' l A = None \<longleftrightarrow> A (var_of_lit l) = None"
      by (cases l) auto


    lemma assign_all_negated_refine[refine]:
      assumes [simp]: "Ai=A"
      assumes [simp]: "Ci=C"
      assumes [simp]: "F = dom W"
      assumes [simp, intro]: "finite C"
      assumes no_taut: "\<forall>l\<in>C. neg_lit l\<notin>C"
      assumes "twl_invar_no_conf DB W Ai"
      shows "twl_assign_all_negated W Ai Ci \<le>\<Down>(br twl_A_\<alpha> (twlR_bt_invar A F)) (RETURN (assign_all_negated A C))"
    proof -
      interpret twl_invar_no_conf DB W Ai by fact
      from init_backtrack interpret twl_bt_invar DB W Ai W Ai "{}" False "{}" .
      
      let ?UD = "{l\<in>C. sem_lit' l A = None}"

      have AUX1: "twl_bt_invar DB W A W (assign_all_negated A C) ?UD False (var_of_lit ` ?UD)"
        apply (unfold_locales; try_lasms)
        subgoal using watched_invar by auto
        subgoal for i
        proof simp
          assume "i\<in>dom W" then obtain w1 w2 where Wi: "W i = Some (w1,w2)" by auto
          assume "sem_clause' (CL i) (assign_all_negated A C) = Some False"
          with W_mem[OF Wi] have "sem_lit' w1 (assign_all_negated A C) = Some False" 
            and "sem_lit' w2 (assign_all_negated A C) = Some False"
            by (auto simp: sem_clause'_false_conv)
          hence 
            " (sem_lit' w1 A = Some False \<and> sem_lit' w2 A = Some False)
            \<or> (w1\<in>?UD \<or> w2\<in>?UD)" (is "?C1 \<or> ?C2")
            by (auto elim!: sem_lit_assign_all_negated_cases)
          thus "twl_invar_defs.is_covered W ?UD i"
          proof
            assume ?C2 thus ?thesis using Wi 
              by (auto simp: twl_invar_defs.is_covered_def watched_def)
          next
            assume ?C1 
            with watched_invar[OF _ Wi] have False by auto
            thus ?thesis ..
          qed
        qed
        subgoal for i
        proof simp
          assume "i\<in>dom W" then obtain w1 w2 where Wi: "W i = Some (w1,w2)" by auto

          have [simp]: "twl_invar_defs.is_covered W P i \<longleftrightarrow> w1\<in>P \<or> w2\<in>P" for P
            using Wi
            by (auto simp: twl_invar_defs.is_covered_def watched_def)

          assume UNIT: "is_unit_clause (assign_all_negated A C) (CL i)"
          from unit_contains_no_true[OF this] W_mem[OF Wi] 
          have [simp]: 
            "sem_lit' w1 (assign_all_negated A C) \<noteq> Some True"
            "sem_lit' w2 (assign_all_negated A C) \<noteq> Some True"
            by auto
          hence [simp]: "sem_lit' w1 A \<noteq> Some True" "sem_lit' w2 A \<noteq> Some True"
            using sem_lit_assign_all_negated_pres_decided by blast+


          have "twl_invar_defs.is_covered W ?UD i 
            \<or>  (sem_lit' w1 (assign_all_negated A C) = sem_lit' w1 A 
              \<and> sem_lit' w2 (assign_all_negated A C) = sem_lit' w2 A)" (is "_ \<or> ?C2")
            apply (cases "sem_lit' w1 (assign_all_negated A C)"; cases "sem_lit' w2 (assign_all_negated A C)")
            apply (auto elim!: sem_lit_assign_all_negated_cases simp: sem_lit_assign_all_negated_none_iff)
            done
          moreover {
            assume ?C2
            with watched_invar[OF _ Wi] have 
              NF1: "sem_lit' w1 (assign_all_negated A C) \<noteq> Some False" and
              NF2: "sem_lit' w2 (assign_all_negated A C) \<noteq> Some False"
              by auto
            with UNIT two_nfalse_not_unit[OF _ _ _ NF1 NF2] W_dist_mem[OF Wi] have False by auto
          } ultimately show "twl_invar_defs.is_covered W ?UD i" by blast
        qed  
        subgoal by (auto simp: sem_lit_assign_all_negated_assign[OF no_taut])
        subgoal for w1 w2 i 
          using watched_invar
          by (auto 
            elim!: sem_lit_assign_all_negated_cases 
            dest!: sem_lit_assign_all_negated_neqv)
        subgoal
          unfolding assign_all_negated_def
          by (force 
              simp: map_add_def restrict_map_def sem_lit'_none_conv 
              split: split_if)
        done
      show ?thesis
        unfolding twl_assign_all_negated_def
        using init_backtrack AUX1
        by (auto simp: br_def twl_A_\<alpha>_def twlR_bt_invar_def Let_def)
    qed

    lemma twl_has_rup_refine[refine]: 
      assumes [simp]: "dom W = F"
      assumes [simplified,simp]: "(Ai,A)\<in>Id"
      assumes [simplified,simp]: "(Ci,C)\<in>Id"
      assumes [simp]: "twl_invar_no_conf DB W A"
      shows "twl_has_rup W Ai Ci 
        \<le> \<Down>(br fst (\<lambda>(_,Wr,Ar). dom Wr = F \<and> Ar = A \<and> twl_invar_no_conf DB Wr Ar)) 
        (has_rup2 F A C)"
    proof -
      interpret twl_invar_no_conf DB W A by fact

      show ?thesis
        unfolding twl_has_rup_def has_rup2_def
        apply (refine_rcg refl)
        apply (vc_solve solve: asm_rl simp: br_def twlR_bt_invar_def twlR_bt_invar_conp_def twl_A_\<alpha>_def)
        subgoal premises prems for W P TR W' A' P' TR' CN' W\<^sub>b W\<^sub>b'
        proof (intro conjI)
          from prems interpret I': twl_bt_invar_conp DB W\<^sub>b' A W' A' P' CN' TR' by simp

          show "(\<exists>i\<in>I'.F. sem_clause' (CL i) A' = Some False) = CN'"
            by (simp add: I'.cn_precise)

          show "A' |` (- TR') = A" by (simp add: I'.AB_EQ)

          show "twl_invar_no_conf DB W' (A' |` (- TR'))"
            by (rule I'.backtrack')
        qed
        done
    qed
          
    definition "twl_has_rat W A Ci \<equiv> do {
      ASSERT (up_no_conflict (CL`dom W) A);
      let C = CL Ci;
      if C={} then RETURN (False,W,A)
      else do {
        reslit \<leftarrow> OBTAIN (\<lambda>l. l\<in>C);
        if sem_lit' reslit A \<noteq> Some False then do {
          FOREACHc  
            { j\<in>dom W. neg_lit reslit \<in> CL j } (\<lambda>(flag,_,_). flag) (\<lambda>j (_,W,A). do {
              twl_has_rup W A (CL j-{neg_lit reslit} \<union> C)
          }) (True,W,A)
        } else RETURN (False,W,A)
      }
    }"  

    lemma twl_has_rat_refine[refine]:
      assumes [simp]: "dom W = F"
      assumes [simplified,simp]: "(Ai,A)\<in>Id"
      assumes [simplified,simp]: "(Ci,C)\<in>Id"
      assumes [simp]: "twl_invar_no_conf DB W A"
      shows "twl_has_rat W Ai Ci 
        \<le> \<Down>(br fst (\<lambda>(_,Wr,Ar). dom Wr = F \<and> Ar = A \<and> twl_invar_no_conf DB Wr Ar)) 
        (has_rat2 F A C)"
      unfolding twl_has_rat_def has_rat2_def
      apply (refine_rcg inj_on_id)
      apply refine_dref_type
      apply (auto simp: br_def)
      done


    definition "twl_has_rup_or_rat W A Ci \<equiv> do {
      ASSERT (up_no_conflict (CL`dom W) A);
      (rup,W,A) \<leftarrow> twl_has_rup W A (CL Ci);
      if rup then RETURN (True,W,A)
      else do {
        (rat,W,A) \<leftarrow> twl_has_rat W A Ci;
        RETURN (rat,W,A)
      }
    }"

    lemma twl_has_rup_or_rat_refine[refine]:
      assumes [simp]: "dom W = F"
      assumes [simplified,simp]: "(Ai,A)\<in>Id"
      assumes [simplified,simp]: "(Ci,C)\<in>Id"
      assumes [simp]: "twl_invar_no_conf DB W A"
      shows "twl_has_rup_or_rat W Ai Ci 
        \<le> \<Down>(br fst (\<lambda>(_,Wr,Ar). dom Wr = F \<and> Ar = A \<and> twl_invar_no_conf DB Wr Ar)) 
        (has_rup_or_rat2 F A C)"
      unfolding twl_has_rup_or_rat_def has_rup_or_rat2_def
      apply (refine_rcg inj_on_id)
      apply (auto simp: br_def)
      done
    
      
    definition "twl_add_clause i W A P \<equiv> do {
      ASSERT (i\<in>dom DB \<and> i\<notin>dom W);
      let C = CL i;
      if is_conflict_clause A C then
        RETURN (True,W,A,P)
      else if is_unit_clause A C then do {
        l \<leftarrow> OBTAIN (\<lambda>l. is_unit_lit A C l);
        let A = assign_lit A l;
        RETURN (False,W,A,insert (neg_lit l) P)
      } else if sem_clause' C A = Some True then
        RETURN (False,W,A,P)
      else do {
        (w1,w2) \<leftarrow> OBTAIN (\<lambda>(w1,w2). w1\<in>C \<and> w2\<in>C \<and> w1\<noteq>w2 \<and> sem_lit' w1 A = None \<and> sem_lit' w2 A = None);
        RETURN (False,W(i\<mapsto>(w1,w2)),A,P)
      }
    }"

    definition "add_clause_rel' \<equiv> br 
      (\<lambda>(flag,W,A,P). (flag,dom W,A)) 
      (\<lambda>(flag,W,A,P). \<not>flag \<longrightarrow> twl_invar_ni DB W A P False)"

    lemma twl_add_clause_refine[refine]:
      assumes "((W,Ai,P),(F,A)) \<in> WAP_rel"
      assumes [simplified,simp]: "(ii,i)\<in>Id"
      shows "twl_add_clause ii W Ai P \<le>\<Down>add_clause_rel' (add_clause2 i F A)"
    proof -
      from assms(1) have 
        DOMW_EQ[simp]: "dom W = F" 
        and [simp]: "Ai=A" 
        and [simp]: "twl_invar_ni DB W A P False"
        by (auto simp: WAP_rel_def in_br_conv)

      interpret twl_invar_ni DB W A P False by fact 

      show ?thesis  
        unfolding twl_add_clause_def add_clause2_def
        apply (refine_vcg bind_refine')
        apply refine_dref_type
        apply (vc_solve simp: add_clause_rel'_def in_br_conv solve: asm_rl[of "Ex _"])
      proof -  
        fix C l
        assume "inres (OBTAIN (is_unit_lit A C)) l" "nofail (OBTAIN (is_unit_lit A C))"
        hence "is_unit_lit A C l"
          by (auto simp: refine_pw_simps)
  
        hence UNDEC: "sem_lit' l A = None" by (auto simp: is_unit_lit_def)
  
        note [simp del] = DOMW_EQ
  
        show "twl_invar_ni DB W (assign_lit A l) (insert (neg_lit l) P) False"  
          apply (unfold_locales; try_lasms)
          subgoal for i 
          proof simp
            assume "i\<in>dom W" and FALSE: "sem_clause' (CL i) (assign_lit A l) = Some False"
            then obtain w1 w2 where Wi: "W i = Some (w1,w2)" using DOMW_EQ[symmetric] by auto
            
            from FALSE W_mem[OF Wi] Wi have 
              "neg_lit l \<in> watched W i 
              \<or> (sem_lit' w1 A = Some False \<and> sem_lit' w2 A = Some False)"
              by (auto 
                simp: sem_clause'_false_conv sem_lit'_assign_conv watched_def 
                split: split_if_asm)
            moreover {
              assume "neg_lit l \<in> watched W i"
              hence "twl_invar_defs.is_covered W (insert (neg_lit l) P) i"
                by (auto simp: twl_invar_defs.is_covered_def)
            } moreover {
              assume "sem_lit' w1 A = Some False \<and> sem_lit' w2 A = Some False"
              with watched_invar[OF _ Wi] Wi have "twl_invar_defs.is_covered W (insert (neg_lit l) P) i"
                by (auto simp: twl_invar_defs.is_covered_def watched_def)
            } ultimately show "twl_invar_defs.is_covered W (insert (neg_lit l) P) i"
              by blast
          qed    
          subgoal for i 
          proof simp
            assume "i\<in>dom W" and UNIT: "is_unit_clause (assign_lit A l) (CL i)"
            then obtain w1 w2 where Wi: "W i = Some (w1,w2)" using DOMW_EQ[symmetric] by auto
            
            from UNIT W_mem[OF Wi] have [simp]:
              "sem_lit' w1 A \<noteq> Some True"
              "sem_lit' w2 A \<noteq> Some True"
              using UNDEC assign_undec_pres_dec_lit unit_contains_no_true 
              apply -
              apply blast+
              done
  
            from UNIT W_dist_mem[OF Wi] Wi have 
              "neg_lit l \<in> watched W i 
              \<or> (sem_lit' w1 A = Some False \<or> sem_lit' w2 A = Some False)"
              using two_nfalse_not_unit[of w1 "CL i" w2 "assign_lit A l"]
              by (fastforce 
                simp: sem_lit'_assign_conv watched_def 
                split: split_if_asm)
            moreover {
              assume "neg_lit l \<in> watched W i"
              hence "twl_invar_defs.is_covered W (insert (neg_lit l) P) i"
                by (auto simp: twl_invar_defs.is_covered_def)
            } moreover {
              assume "sem_lit' w1 A = Some False \<or> sem_lit' w2 A = Some False"
              with watched_invar[OF _ Wi] Wi have "twl_invar_defs.is_covered W (insert (neg_lit l) P) i"
                by (auto simp: twl_invar_defs.is_covered_def watched_def)
            } ultimately show "twl_invar_defs.is_covered W (insert (neg_lit l) P) i"
              by blast
          qed    
          subgoal for ll using pending_false[of ll] UNDEC by (auto simp: sem_lit'_assign_conv)
          subgoal for w1 w2 i using watched_invar[of i w1 w2]
            by (auto simp: sem_lit'_assign_conv UNDEC)
          done
      next
        fix C
        assume "sem_clause' C A \<noteq> Some False" and NTRUE: "sem_clause' C A \<noteq> Some True"
        then obtain w1 where W1: "w1\<in>C" "sem_lit' w1 A = None"
          by (force simp: sem_clause'_def split: split_if_asm)
          
        assume "\<not> is_unit_clause A C"   
        then obtain w2 where W2: "w2\<in>C" "w1\<noteq>w2" "sem_lit' w2 A \<noteq> Some False"
          using W1 by (force simp: is_unit_clause_def is_unit_lit_def sem_clause'_false_conv)
        with NTRUE have W2': "sem_lit' w2 A = None" by (cases "sem_lit' w2 A") (auto simp: sem_clause'_true_conv)
  
        with W1 W2 W2' show 
          "\<exists>w1. w1 \<in> C \<and> (\<exists>w2. w2 \<in> C \<and> w1 \<noteq> w2 \<and> sem_lit' w1 A = None \<and> sem_lit' w2 A = None)"
          by blast
      next
        note [simp del] = DOMW_EQ
        note [simp] = DOMW_EQ[symmetric]
  
        fix w1 w2 C    
        assume W: "w1\<in>C" "w2\<in>C" "w1\<noteq>w2" "sem_lit' w1 A = None" "sem_lit' w2 A = None"
        assume DBi: "DB i = Some C" and NIF: "i\<notin>F"
        
        assume [simp]: "sem_clause' C A \<noteq> Some False" "\<not> is_unit_clause A C"
  
        show "twl_invar_ni DB (W(i \<mapsto> (w1, w2))) A P False"
          apply (unfold_locales; try_lasms)
          subgoal using W_valid DBi by auto
          subgoal for w1' w2' i' using W_dist_mem[of i' w1' w2'] NIF W DBi
            by (auto split: split_if_asm)
          subgoal for i' using conflict_covered[of i'] DBi NIF 
            by (auto simp: twl_invar_defs.is_covered_def watched_def)
          subgoal for i' using unit_covered[of i'] DBi NIF 
            by (auto simp: twl_invar_defs.is_covered_def watched_def)
          subgoal for w1' w2' i' using watched_invar[of i' w1' w2'] W 
            by (auto split: split_if_asm)
          done
      qed    
    qed  
        
    definition "twl_load_clauses F\<^sub>0 \<equiv> do {
      let W = Map.empty;
      let A = Map.empty;
      let P = {};
      nfoldli F\<^sub>0 (\<lambda>(conflict,_,_,_). \<not>conflict) (\<lambda>C (_,W,A,P). 
        twl_add_clause C W A P
      ) (False,W,A,P)
    }"

    lemma twl_invar_empty: "twl_invar_ni DB Map.empty Map.empty {} False"
      by (unfold_locales; auto)


    lemma twl_load_clauses_refine[refine]:
      assumes [refine]: "(F\<^sub>0i,F\<^sub>0) \<in> \<langle>Id\<rangle>list_rel"
      shows "twl_load_clauses F\<^sub>0i \<le> \<Down>add_clause_rel' (load_clauses2 F\<^sub>0)"
      unfolding twl_load_clauses_def load_clauses2_def
      apply refine_rcg
      apply (auto simp: add_clause_rel'_def WAP_rel_def in_br_conv twl_invar_empty)
      done

    definition "twl_delete_clause i W A \<equiv> do {
      RETURN (W|`(-{i}),A)
    }"
      
    definition "nc_rel \<equiv> br (\<lambda>(W,A). (dom W,A)) (\<lambda>(W,A). twl_invar_no_conf DB W A)"

    definition "nc_rel' \<equiv> br (\<lambda>(flag,W,A). (flag,dom W,A)) (\<lambda>(flag,W,A). flag=(0::int) \<longrightarrow> twl_invar_no_conf DB W A)"


    lemma twl_delete_clause_refine[refine]:
      assumes [simplified,simp]: "(ii,i)\<in>Id"
      assumes "((W,Ai), (F,A))\<in>nc_rel"
      shows "twl_delete_clause ii W Ai \<le> \<Down>nc_rel (delete_clause2 i F A)"
    proof -
      from assms(2) have 
        [simp]: "F=dom W" "Ai=A" and "twl_invar_no_conf DB W A"
        by (auto simp: nc_rel_def in_br_conv)
        
      interpret twl_invar_no_conf DB W A by fact

      show ?thesis
        unfolding twl_delete_clause_def delete_clause2_def
        apply refine_rcg
        apply (vc_solve simp: nc_rel_def in_br_conv)
        subgoal
          apply (unfold_locales; try_lasms)
          subgoal using W_valid by auto
          subgoal for w1 w2 i' using W_dist_mem[of i' w1 w2] by (auto simp: restrict_map_eq)
          subgoal for i' using conflict_covered[of i'] 
            by (auto simp: twl_invar_defs.is_covered_def)
          subgoal for i' using unit_covered[of i'] 
            by (auto simp: twl_invar_defs.is_covered_def)
          subgoal for w1 w2 i' using watched_invar[of i' w1 w2] 
            by (auto simp: restrict_map_eq)
          done
        done
    qed    
      

    definition "twl_verify F\<^sub>0 prf \<equiv> do {
      (conf,W,A,P) \<leftarrow> twl_load_clauses F\<^sub>0;   (* Load clauses *)
  
      if conf then RETURN UNSAT           (* This may already reveal conflict *) 
      else do {
        (W,A,_,conf) \<leftarrow> twl_prop_unit_ntr W A P;      (* Propagate units *)
    
        let conf=conf;
        if conf then
          RETURN UNSAT (* Conflict from initial clauses by unit propagation *)
        else do {  
          (* No conflicts initially. Iterate over proof *)
          (flag,W,A) \<leftarrow> nfoldli prf (\<lambda>(flag,_,_). flag=0) (\<lambda>s (_,W,A). do {
            case s of
              (False,C) \<Rightarrow> do {
                (* Check if add-clause has RUP or RAT *)
                (ror,W,A) \<leftarrow> twl_has_rup_or_rat W A C;
                if ror then do {
                  (* Add the clause. This may find the clause to be a conflict clause. *)
                  (conf,W,A,P) \<leftarrow> twl_add_clause C W A {};
                  if conf then RETURN (1,W,A) (* Added conflict clause *)
                  else do {
                    (* If no immediate conflict, do unit propagation *)
                    (W,A,_,conf) \<leftarrow> twl_prop_unit_ntr W A P;
                    let conf=conf;
                    if conf then 
                      RETURN (1,W,A) (* Unit propagation found a conflict *)
                    else
                      RETURN (0,W,A) (* Unit propagation did not find a conflict *)
                  }
                } else
                  RETURN (-1, W, A) (* Attempt to add clause without RUP or RAT *)
              }
            | (True,C) \<Rightarrow> do {
                (W,A) \<leftarrow> twl_delete_clause C W A;
                RETURN (0,W,A)
              }  
          }) (0::int,W,A);
  
          if flag = 1 then RETURN UNSAT
          else RETURN ERROR
        }
      }  
    }"

    lemma twl_CN_refine[refine]:
      assumes "((W,A,P,CN),A)\<in>WAPC_relA_conp F"
      shows "RETURN CN \<le> \<Down>Id (has_conflict_spec2 F A)"
      using assms unfolding WAPC_relA_conp_def in_br_conv
    proof clarsimp
      assume "twl_invar_conp DB W A P CN"
      then interpret twl_invar_conp DB W A P CN .

      show "RETURN CN \<le> has_conflict_spec2 (dom W) A"
        by (auto simp: has_conflict_spec2_def cn_precise)
    qed    
      
             
    lemma twl_verify_refine[refine]:
      assumes [refine]: "(F',F) \<in> \<langle>Id\<rangle>list_rel"
      assumes [refine]: "(prf',prf) \<in> \<langle>Id\<rangle>list_rel"
      shows "twl_verify F' prf' \<le> \<Down>Id (verify2 F prf)"
    proof -
      have [refine_dref_RELATES]: "RELATES nc_rel'" 
        by (simp add: RELATES_def)

      {
        fix W A P
        assume "twl_invar_conp DB W A P False"
        then interpret twl_invar_conp DB W A P False .
        from no_conf_no_pending have [simp]: "P={}" by simp

        have "twl_invar_no_conf DB W A"
          apply (unfold_locales; try_lasms)
          subgoal using cn_precise by auto
          subgoal using unit_covered by auto
          subgoal using watched_invar by auto
          done
      } note aux1=this 

      {
        fix W A
        assume "twl_invar_no_conf DB W A"
        then interpret twl_invar_no_conf DB W A .
        have "twl_invar_ni DB W A {} False"
          by unfold_locales
      } note aux2=this


      show ?thesis
        supply [[goals_limit = 1]]
        unfolding twl_verify_def verify2_def
        apply (refine_rcg bind_refine')
        apply refine_dref_type
        apply (auto 
          simp: in_br_conv add_clause_rel'_def 
          simp: WAP_rel_def WAPC_relA_conp_def
          simp: nc_rel'_def nc_rel_def aux1 aux2
        ) (* Takes its time. TODO: Could be optimized by not unfolding all 
            the _rels, but showing lemmas about the rels *)
        done
    qed  



  end


oops
 using FB_EQ IB.conflict_covered IB.is_covered_def by blast

oops
  xxx, now do other operations ... up to verify3!





  record 'a state =
    F :: "'a cnf"
    A :: "'a \<rightharpoonup> bool"
    steps :: "'a proof_step list"


  definition "proof_step S \<equiv> do {
    ASSERT (steps S \<noteq> []);
    let (s,S) = (hd (steps S), S\<lparr>steps := tl (steps S)\<rparr>);
    
    case s of
      Add C \<Rightarrow> do {
        
        RETURN (S\<lparr> F := insert C (F S) \<rparr>)
      }
    | Del C \<Rightarrow> RES {S\<lparr> F := F S - {C} \<rparr>, S}
  }"    







end
