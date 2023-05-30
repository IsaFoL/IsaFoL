theory Ground_Critical_Pairs_String_Vars
  imports
    TRS.Trs
    Ground_Critical_Pairs
begin

lemma ballI2: "(\<And>x y. (x, y) \<in> A \<Longrightarrow> P x y) \<Longrightarrow> \<forall>(x, y) \<in> A. P x y"
  by auto

abbreviation is_ground_trm where
  "is_ground_trm t \<equiv> vars_term t = {}"

(* lemma mem_ground_critical_pairs_if_mem_critical_pairs:
  fixes s t :: "('f, string) term"
  assumes
    ground_R: "\<forall>(s, t) \<in> R. is_ground_trm s \<and> is_ground_trm t" and
    crit_pair: "(b, s, t) \<in> critical_pairs R R"
  shows "(s, t) \<in> ground_critical_pairs R"
proof -
  from crit_pair obtain ctxt l r l' r' l'' \<sigma> \<tau> where
    "b = (ctxt = \<box>)" and
    "s = (ctxt \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>" and
    "t = r \<cdot> \<sigma>" and
    "(l, r) \<in> R" and
    "(l', r') \<in> R" and
    "l = ctxt\<langle>l''\<rangle>" and
    "is_Fun l''" and
    mgu: "mgu_var_disjoint_string l'' l' = Some (\<sigma>, \<tau>)"
    unfolding critical_pairs_def by auto

  from ground_R have "is_ground_trm l" and "is_ground_trm r"
    using \<open>(l, r) \<in> R\<close> by auto

  from ground_R have "is_ground_trm l'" and "is_ground_trm r'"
    using \<open>(l', r') \<in> R\<close> by auto

  have "vars_ctxt ctxt = {}" and "is_ground_trm l''"
    using \<open>is_ground_trm l\<close>
    unfolding \<open>l = ctxt\<langle>l''\<rangle>\<close>
    by (simp_all add: vars_term_ctxt_apply)

  have "l'' = l'"
    using mgu \<open>is_ground_trm l''\<close> \<open>is_ground_trm l'\<close>
    by (metis empty_iff mgu_var_disjoint_string_sound subst_apply_term_empty term_subst_eq_conv)

  show ?thesis
    unfolding ground_critical_pairs_def mem_Collect_eq
  proof (intro exI conjI)
    show "(ctxt\<langle>l''\<rangle>, r) \<in> R"
      using \<open>(l, r) \<in> R\<close>
      unfolding \<open>l = ctxt\<langle>l''\<rangle>\<close>
      by argo
  next
    show "(l'', r') \<in> R"
      unfolding \<open>l'' = l'\<close>
      using \<open>(l', r') \<in> R\<close>
      by argo
  next
    show "(s, t) = (ctxt\<langle>r'\<rangle>, r)"
      unfolding \<open>s = (ctxt \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>\<close> \<open>t = r \<cdot> \<sigma>\<close>
      using \<open>vars_ctxt ctxt = {}\<close> \<open>is_ground_trm r'\<close> \<open>is_ground_trm r\<close>
      by (metis ctxt_subst_eq ctxt_subst_id empty_iff subst.cop_nil term_subst_eq_conv)
  qed
qed

lemma mem_critical_pairs_if_mem_ground_critical_pairs:
  fixes s t :: "('f, string) term"
  assumes
    ground_R: "\<forall>(s, t) \<in> R. is_ground_trm s \<and> is_ground_trm t" and
    crit_pair: "(s, t) \<in> ground_critical_pairs R"
  shows "\<exists>b. (b, s, t) \<in> critical_pairs R R"
proof -
  from crit_pair obtain ctxt l r\<^sub>1 r\<^sub>2 where
    "(s, t) = (ctxt\<langle>r\<^sub>2\<rangle>, r\<^sub>1)" and
    "(ctxt\<langle>l\<rangle>, r\<^sub>1) \<in> R" and
    "(l, r\<^sub>2) \<in> R"
    unfolding ground_critical_pairs_def by auto

  from ground_R have "vars_ctxt ctxt = {}" and "is_ground_trm l" and "is_ground_trm r\<^sub>1"
    unfolding atomize_conj
    using \<open>(ctxt\<langle>l\<rangle>, r\<^sub>1) \<in> R\<close> vars_term_ctxt_apply by fastforce

  from ground_R have "is_ground_trm r\<^sub>2"
    using \<open>(l, r\<^sub>2) \<in> R\<close> by auto

  obtain \<mu>\<^sub>1 \<mu>\<^sub>2 where mgu: "mgu_var_disjoint_string l l = Some (\<mu>\<^sub>1, \<mu>\<^sub>2)"
    using mgu_var_disjoint_string_complete by blast

  show ?thesis
  proof (intro exI critical_pairsI)
    show "(ctxt\<langle>l\<rangle>, r\<^sub>1) \<in> R"
      using \<open>(ctxt\<langle>l\<rangle>, r\<^sub>1) \<in> R\<close> .
  next
    show "(l, r\<^sub>2) \<in> R"
      using \<open>(l, r\<^sub>2) \<in> R\<close> .
  next
    show "ctxt\<langle>l\<rangle> = ctxt\<langle>l\<rangle>" ..
  next
    show "is_Fun l"
      using \<open>is_ground_trm l\<close> by fastforce
  next
    show "mgu_var_disjoint_string l l = Some (\<mu>\<^sub>1, \<mu>\<^sub>2)"
      using mgu .
  next
    show "t = r\<^sub>1 \<cdot> \<mu>\<^sub>1"
      using \<open>(s, t) = (ctxt\<langle>r\<^sub>2\<rangle>, r\<^sub>1)\<close> \<open>is_ground_trm r\<^sub>1\<close>
      by (simp add: subst_apply_term_ident)
  next
    show "s = (ctxt \<cdot>\<^sub>c \<mu>\<^sub>1)\<langle>r\<^sub>2 \<cdot> \<mu>\<^sub>2\<rangle>"
      using \<open>(s, t) = (ctxt\<langle>r\<^sub>2\<rangle>, r\<^sub>1)\<close> \<open>vars_ctxt ctxt = {}\<close> \<open>is_ground_trm r\<^sub>2\<close>
      by (metis Pair_inject ctxt_subst_eq ctxt_subst_id empty_iff inf_bot_left
          subst_apply_term_ident)
  next
    show "(ctxt = \<box>) = (ctxt = \<box>)" ..
  qed
qed

lemma foo:
  assumes ground_R: "\<forall>(s, t) \<in> R. is_ground_trm s \<and> is_ground_trm t"
  shows "\<And>r. r \<in> rewrite_steps R \<Longrightarrow> r \<in> rstep R"
    by (smt (verit, del_insts) mem_Collect_eq rewrite_steps_def rstep_ctxt subset_iff subset_rstep) *)

lemma converse_rewrite_step: "(rewrite_steps R)\<inverse> = rewrite_steps (R\<inverse>)"
  by (auto simp: rewrite_steps_def)

lemma subset_rewrite_steps: "R \<subseteq> rewrite_steps R"
  apply (rule Set.subsetI)
  unfolding rewrite_steps_def mem_Collect_eq
  by (metis ctxt_apply_term.simps(1) prod.exhaust)

lemma ground_critical_pairs_fork:
  assumes cp: "(l, r) \<in> ground_critical_pairs R"
  shows "(r, l) \<in> (rewrite_steps R)\<inverse> O rewrite_steps R"
proof -
  from cp [unfolded ground_critical_pairs_def, simplified]
  obtain ctxt t r\<^sub>1 t' where "l = ctxt\<langle>t'\<rangle>" and "(ctxt\<langle>t\<rangle>, r) \<in> R" and "(t, t') \<in> R"
    by metis
    
  have "(r, ctxt\<langle>t\<rangle>) \<in> (rewrite_steps R)\<inverse>"
    using \<open>(ctxt\<langle>t\<rangle>, r) \<in> R\<close> subset_rewrite_steps by blast
  moreover have "(ctxt\<langle>t\<rangle>, l) \<in> rewrite_steps R"
    using \<open>(t, t') \<in> R\<close> \<open>l = ctxt\<langle>t'\<rangle>\<close> rewrite_steps_def by fast
  ultimately show ?thesis by auto
qed

lemma ground_critical_pairs_complete:
  fixes R :: "('f, string) trs"
  assumes cp: "(l, r) \<in> ground_critical_pairs R"
    and no_join: "(l, r) \<notin> (rewrite_steps R)\<^sup>\<down>"
  shows "\<not> WCR (rewrite_steps R)"
proof (rule notI)
  assume wcr: "WCR (rewrite_steps R)"
  moreover from ground_critical_pairs_fork[OF cp] obtain u where
    ul: "(u, l) \<in> rewrite_steps R" and ur: "(u, r) \<in> rewrite_steps R"
    by auto
  ultimately show False
    using no_join
    unfolding WCR_on_def
    by simp
qed



lemma rewrite_steps_closed_ctxt:
  assumes "(s, t) \<in> (rewrite_steps R)\<^sup>*"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (rewrite_steps R)\<^sup>*"
proof -
  from assms obtain n where "(s,t) \<in> (rewrite_steps R)^^n"
    using rtrancl_is_UN_relpow by auto
  then show ?thesis
  proof (induct n arbitrary: s)
    case 0 then show ?case by auto
  next
    case (Suc n)
    from relpow_Suc_D2[OF \<open>(s,t) \<in> (rewrite_steps R)^^Suc n\<close>] obtain u
      where "(s,u) \<in> (rewrite_steps R)" and "(u,t) \<in> (rewrite_steps R)^^n" by auto
    from \<open>(s,u) \<in> (rewrite_steps R)\<close> have "(C\<langle>s\<rangle>,C\<langle>u\<rangle>) \<in> (rewrite_steps R)"
      apply (simp add: rewrite_steps_def)
      using ctxt_ctxt by blast
    from Suc and \<open>(u,t) \<in> (rewrite_steps R)^^n\<close> have "(C\<langle>u\<rangle>,C\<langle>t\<rangle>) \<in> (rewrite_steps R)\<^sup>*" by simp
    with \<open>(C\<langle>s\<rangle>,C\<langle>u\<rangle>) \<in> (rewrite_steps R)\<close> show ?case by auto
 qed
qed


lemma critical_pairs_main:
  fixes R :: "('f, string) trs"
  assumes ground_R: "\<forall>(s, t) \<in> R. is_ground_trm s \<and> is_ground_trm t"
  assumes st1: "(s, t1) \<in> rewrite_steps R" and st2: "(s, t2) \<in> rewrite_steps R"
  shows "(t1, t2) \<in> join (rewrite_steps R) \<or>
    (\<exists> ctxt l r. t1 = ctxt\<langle>l\<rangle> \<and> t2 = ctxt\<langle>r\<rangle> \<and>
      ((l, r) \<in> ground_critical_pairs R \<or> (r, l) \<in> ground_critical_pairs R))"
proof -
  let ?R = "rewrite_steps R"
  let ?CP = "ground_critical_pairs R"
  from st1 obtain C1 l1 r1 where
    lr1: "(l1, r1) \<in> R" and s1: "s = C1\<langle>l1\<rangle>" and t1: "t1 = C1\<langle>r1\<rangle>"
    by (auto simp: rewrite_steps_def)
  from st2 obtain C2 l2 r2 where
    lr2: "(l2, r2) \<in> R" and s2: "s = C2\<langle>l2\<rangle>" and t2: "t2 = C2\<langle>r2\<rangle>"
    by (auto simp: rewrite_steps_def)
  from s1 s2 have id: "C1\<langle>l1\<rangle> = C2\<langle>l2\<rangle>"
    by simp
  let ?q = "\<lambda>s t. (s, t) \<in> join ?R \<or> (\<exists>C l r. s = C\<langle>l\<rangle> \<and> t = C\<langle>r\<rangle> \<and> ((l, r) \<in> ?CP \<or> (r, l) \<in> ?CP))"
  let ?p = "\<lambda>(C1, C2). \<forall>l1 r1 l2 r2.
    (l1, r1) \<in> R \<longrightarrow> (l2, r2) \<in> R \<longrightarrow> (C1\<langle>l1\<rangle> = C2\<langle>l2\<rangle>) \<longrightarrow> ?q C1\<langle>r1\<rangle> C2\<langle>r2\<rangle>"
  have "?p C12" for C12 :: "('f, string) ctxt \<times> ('f, string) ctxt"
  proof -
    let ?m = "[\<lambda>(C1, C2). size C1 + size C2, \<lambda> (C1, C2). size C1]"
    show "?p C12"
    proof (induct rule: wf_induct [OF wf_measures [of ?m], of ?p])
      case (1 C12)
      obtain C1 C2 where C12: "C12 = (C1, C2)" by force
      show "?p C12" unfolding C12 split
      proof (intro allI impI)
        fix l1 r1 l2 r2
        assume lr1: "(l1, r1) \<in> R" and lr2: "(l2, r2) \<in> R" and id: "C1\<langle>l1\<rangle> = C2\<langle>l2\<rangle>"
        show "?q (C1\<langle>r1\<rangle>) (C2\<langle>r2\<rangle>)"
        proof (cases C1)
          case Hole note C1 = this
          with id have id: "l1 = C2\<langle>l2\<rangle>" by simp
          let ?p = "hole_pos C2"
          show ?thesis
          proof (cases "?p \<in> poss l1 \<and> is_Fun (l1 |_ ?p)")
            case True
            then have p: "?p \<in> poss l1" by auto
            from ctxt_supt_id [OF p] obtain D where Dl1: "D\<langle>l1 |_ ?p\<rangle> = l1"
              and D: "D = ctxt_of_pos_term (hole_pos C2) l1" by blast
            from arg_cong [OF Dl1, of "\<lambda>t. t"]
            have "(D)\<langle>(l1 |_ ?p)\<rangle> = C2\<langle>l2\<rangle>" unfolding id by simp
            from arg_cong [OF this, of "\<lambda> t. t |_ ?p"]
            have "l2 = (D)\<langle>(l1 |_ ?p)\<rangle> |_ ?p" by simp
            also have "... = (D)\<langle>(l1 |_ ?p)\<rangle> |_ (hole_pos (D))"
              using hole_pos_ctxt_of_pos_term [OF p] unfolding D by simp
            also have "... = (l1 |_ ?p)" by (rule subt_at_hole_pos)
            finally have ident: "l2 = l1 |_ ?p" by auto
            have in_cp: "((D)\<langle>r2\<rangle>, r1) \<in> ground_critical_pairs R"
              unfolding ground_critical_pairs_def mem_Collect_eq
              by (metis Dl1 ident lr1 lr2)
            from hole_pos_ctxt_of_pos_term [OF p] D have pD: "?p = hole_pos D" by simp
            from id have C2: "C2 = ctxt_of_pos_term ?p (l1)" by simp
            have "C2\<langle>r2\<rangle> = (ctxt_of_pos_term ?p (l1))\<langle>r2\<rangle>" using C2 by simp
            also have "... = (D)\<langle>r2\<rangle>" unfolding D ..
            finally have C2r\<sigma>: "C2\<langle>r2\<rangle> = D\<langle>r2\<rangle>" .
            from C1 have C1r\<sigma>: "C1\<langle>r1\<rangle> = r1" by simp
            show ?thesis unfolding C2r\<sigma> C1r\<sigma>
            proof (rule disjI2, intro exI, intro conjI)
              show "r1 = \<box>\<langle>r1\<rangle>" by simp
            qed (insert in_cp, auto)
          next
            case False
            hence False
              using ground_R
              using id lr1 vars_term_ctxt_apply by fastforce
            thus ?thesis ..
          qed
        next
          case (More f1 bef1 D1 aft1) note C1 = this
          show ?thesis
          proof (cases C2)
            case Hole note C2 = this
            from C1 C2 have "((C2, C1), C12) \<in> measures ?m" unfolding C12 by auto
            from 1[rule_format, OF this, unfolded prod.case, rule_format, OF lr2 lr1 id[symmetric]]
            show ?thesis
            proof
              assume "(C2\<langle>r2\<rangle>, C1\<langle>r1\<rangle>) \<in> join ?R"
              then show ?thesis by auto
            qed blast
          next
            case (More f2 bef2 D2 aft2) note C2 = this
            let ?n1 = "length bef1"
            let ?n2 = "length bef2"
            note id = id [unfolded C1 C2]
            from id have f: "f1 = f2" by simp
            show ?thesis
            proof (cases "?n1 = ?n2")
              case True
              with id have idb: "bef1 = bef2" and ida: "aft1 = aft2"
                and idD: "D1\<langle>l1\<rangle> = D2\<langle>l2\<rangle>" by auto
              let ?C = "More f2 bef2 \<box> aft2"
              have id1: "C1 = ?C \<circ>\<^sub>c D1" unfolding C1 f ida idb by simp
              have id2: "C2 = ?C \<circ>\<^sub>c D2" unfolding C2 by simp
              have "((D1, D2), C12) \<in> measures ?m" unfolding C12 C1 C2
                by auto
              from 1 [rule_format, OF this, unfolded split, rule_format,
                OF lr1 lr2 idD] have "?q (D1\<langle>r1\<rangle>) (D2\<langle>r2\<rangle>)" by auto
              then show ?thesis
              proof
                assume "(D1\<langle>r1\<rangle>, D2\<langle>r2\<rangle>) \<in> join ?R"
                then obtain s' where seq1: "(D1\<langle>r1\<rangle>, s') \<in> ?R^*"
                and seq2: "(D2\<langle>r2\<rangle>, s') \<in> ?R^*" by auto
                from rewrite_steps_closed_ctxt[OF seq1, of ?C]
                have seq1: "(C1\<langle>r1\<rangle>, ?C\<langle>s'\<rangle>) \<in> ?R^*" unfolding id1 by simp
                from rewrite_steps_closed_ctxt[OF seq2, of ?C]
                have seq2: "(C2\<langle>r2\<rangle>, ?C\<langle>s'\<rangle>) \<in> ?R^*" using id2 by simp
                from seq1 seq2 show ?thesis by auto
              next
                assume "\<exists>C l r. D1\<langle>r1\<rangle> = C\<langle>l\<rangle> \<and> D2\<langle>r2\<rangle> = C\<langle>r\<rangle> \<and> ((l, r) \<in> ?CP \<or> (r, l) \<in> ?CP)"
                then obtain C l r where
                  idD: "D1\<langle>r1\<rangle> = C\<langle>l\<rangle>" "D2\<langle>r2\<rangle> = C\<langle>r\<rangle>" and mem: "((l, r) \<in> ?CP \<or> (r, l) \<in> ?CP)"
                  by blast
                show ?thesis
                  by (rule disjI2, unfold id1 id2, rule exI [of _ "?C \<circ>\<^sub>c C"], intro exI, rule conjI [OF _ conjI [OF _ mem]], insert idD, auto)
              qed
            next
              case False
              let ?p1 = "?n1 # hole_pos D1"
              let ?p2 = "?n2 # hole_pos D2"
              have l2: "C1\<langle>l1\<rangle> |_ ?p2 = l2 \<cdot> Var" unfolding C1 id by simp
              have p12: "?p1  \<bottom> ?p2" using False by simp
              have p1: "?p1 \<in> poss (C1\<langle>l1\<rangle>)" unfolding C1 by simp
              have p2: "?p2 \<in> poss (C1\<langle>l1\<rangle>)" unfolding C1 unfolding id by simp
              let ?one = "replace_at (C1\<langle>l1\<rangle>) ?p1 (r1)"
              have one: "C1\<langle>r1\<rangle> = ?one" unfolding C1 by simp
              have "(?one, replace_at ?one ?p2 (r2)) \<in> rewrite_steps R"
                by (smt (verit, ccfv_threshold) CollectI ctxt_supt_id l2 lr2 p1 p12 p2
                    parallel_poss_replace_at parallel_replace_at_subt_at rewrite_steps_def
                    subst_apply_term_empty)
              then have one: "(C1\<langle>r1\<rangle>, replace_at ?one ?p2 (r2)) \<in> (rewrite_steps R)^*" unfolding one by simp
              have l1: "C2\<langle>l2\<rangle> |_ ?p1 = l1 \<cdot> Var" unfolding C2 id [symmetric] by simp
              have p21: "?p2  \<bottom> ?p1" using False by simp
              have p1': "?p1 \<in> poss (C2\<langle>l2\<rangle>)" unfolding C2 id [symmetric] by simp
              have p2': "?p2 \<in> poss (C2\<langle>l2\<rangle>)" unfolding C2 by simp
              let ?two = "replace_at (C2\<langle>l2\<rangle>) ?p2 (r2)"
              have two: "C2\<langle>r2\<rangle> = ?two" unfolding C2 by simp
              have "(?two, replace_at ?two ?p1 (r1)) \<in> rewrite_steps R"
                by (smt (verit, ccfv_threshold) C1 CollectI More ctxt_supt_id id l1 lr1 p1 p2 p21
                    parallel_poss_replace_at parallel_replace_at_subt_at rewrite_steps_def
                    subst_apply_term_empty)
              then have two: "(C2\<langle>r2\<rangle>, replace_at ?two ?p1 (r1)) \<in> (rewrite_steps R)^*" unfolding two by simp
              have "replace_at ?one ?p2 (r2) = replace_at (replace_at (C1\<langle>l1\<rangle>) ?p2 (r2)) ?p1 (r1)"
                by (rule parallel_replace_at [OF p12 p1 p2])
              also have "... = replace_at ?two ?p1 (r1)" unfolding C1 C2 id ..
              finally have one_two: "replace_at ?one ?p2 (r2) = replace_at ?two ?p1 (r1)" .
              have "(C1\<langle>r1\<rangle>, C2\<langle>r2\<rangle>) \<in> (rewrite_steps R)\<^sup>\<down>"
                using one one_two two by auto
              thus ?thesis ..
            qed
          qed
        qed
      qed
    qed
  qed
  from this[of "(C1, C2)", unfolded split, rule_format, OF lr1 lr2 id]
  show ?thesis unfolding t1 t2 by auto
qed

lemma critical_pairs:
  fixes R :: "('f, string) trs"
  assumes ground_R: "\<forall>(s, t) \<in> R. is_ground_trm s \<and> is_ground_trm t"
  assumes cp: "\<And> l r. (l, r) \<in> ground_critical_pairs R \<Longrightarrow> l \<noteq> r \<Longrightarrow>
    \<exists>s. (l, s) \<in> (rewrite_steps R)\<^sup>* \<and> (r, s) \<in> (rewrite_steps R)\<^sup>*"
  shows "WCR (rewrite_steps R)"
proof (rule WCR_onI)
  let ?R = "rewrite_steps R"
  let ?CP = "ground_critical_pairs R"
  fix s t1 t2
  assume steps: "(s, t1) \<in> ?R" "(s, t2) \<in> ?R"
  let ?p = "\<lambda> s'. (t1, s') \<in> ?R^* \<and> (t2, s') \<in> ?R^*"
  from critical_pairs_main [OF ground_R steps]
  have "\<exists> s'. ?p s'"
  proof (elim disjE)
    assume "\<exists>ctxt l r. t1 = ctxt\<langle>l\<rangle> \<and> t2 = ctxt\<langle>r\<rangle> \<and> ((l, r) \<in> ?CP \<or> (r, l) \<in> ?CP)"
    then obtain C l r where id: "t1 = C\<langle>l\<rangle>" "t2 = C\<langle>r\<rangle>"
      and mem: "(l, r) \<in> ?CP \<or> (r, l) \<in> ?CP" by blast
    show ?thesis
    proof (cases "l = r")
      case True
      then show ?thesis unfolding id by auto
    next
      case False
      from mem show ?thesis
      proof (elim disjE)
        assume mem: "(l, r) \<in> ?CP"
        show "\<exists> s'. ?p s'"
          using cp[OF mem False] id rewrite_steps_closed_ctxt by blast
      next
        assume mem: "(r, l) \<in> ?CP"
        show "\<exists> s'. ?p s'"
          using cp[OF mem] id rewrite_steps_closed_ctxt by blast
      qed
    qed
  qed auto
  thus "(t1, t2) \<in> join ?R" by auto
qed

lemma critical_pair_lemma:
  fixes R :: "('f, string) trs"
  assumes ground_R: "\<forall>(s, t) \<in> R. is_ground_trm s \<and> is_ground_trm t"
  shows "WCR (rewrite_steps R) \<longleftrightarrow>
    (\<forall>(s, t) \<in> ground_critical_pairs R. (s, t) \<in> (rewrite_steps R)\<^sup>\<down>)"
  (is "?l = ?r")
proof
  assume "WCR (rewrite_steps R)"
  thus "\<forall>(s, t) \<in> ground_critical_pairs R. (s, t) \<in> (rewrite_steps R)\<^sup>\<down>"
    using ground_critical_pairs_complete by blast
next
  assume all_cp_joinable: "\<forall>(s, t) \<in> ground_critical_pairs R. (s, t) \<in> (rewrite_steps R)\<^sup>\<down>"
  show "WCR (rewrite_steps R)"
  proof (rule critical_pairs[OF ground_R])
    fix s t
    assume "(s, t) \<in> ground_critical_pairs R"
    with all_cp_joinable have "(s, t) \<in> join (rewrite_steps R)" by auto
    then obtain u where s: "(s, u) \<in> (rewrite_steps R)^*"
      and t: "(t, u) \<in> (rewrite_steps R)^*" by auto
    thus "\<exists>u. (s, u) \<in> (rewrite_steps R)^* \<and> (t, u) \<in> (rewrite_steps R)^*"
      by metis
  qed
qed

(* lemma ground_critical_pair_lemma:
  fixes R :: "('f, string) trs"
  assumes ground_R: "\<forall>(s, t) \<in> R. is_ground_trm s \<and> is_ground_trm t"
  shows "WCR (rewrite_steps R) \<longleftrightarrow> (\<forall> (s, t) \<in> ground_critical_pairs R. (s, t) \<in> (rewrite_steps R)\<^sup>\<down>)"
  using critical_pair_lemma[OF ground_R]
  using mem_critical_pairs_if_mem_ground_critical_pairs[OF ground_R]
  using mem_ground_critical_pairs_if_mem_critical_pairs[OF ground_R] *)
  (* by (metis (no_types, lifting) case_prodD case_prodI2) *)

global_interpretation ground_critical_pair_lemma "undefined :: 'f" "undefined :: string"
proof unfold_locales
  fix R :: "('f, string) trs"
  assume "(\<Union>r \<in> R. vars_rewrite_rule r)= {}"
  hence ground_R: "\<forall>(s, t)\<in>R. is_ground_trm s \<and> is_ground_trm t"
    by (auto simp: vars_rewrite_rule_def)
  show "WCR (rewrite_steps R) = (ground_critical_pairs R \<subseteq> (rewrite_steps R)\<^sup>\<down>)"
    using critical_pair_lemma[OF ground_R] by auto
qed

end