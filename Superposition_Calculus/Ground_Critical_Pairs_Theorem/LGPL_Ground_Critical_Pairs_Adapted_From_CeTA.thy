(*
Copyright 2023 Martin Desharnais

This program is free software: you can redistribute it and/or modify it under
the terms of the GNU Lesser General Public License as published by the Free
Software Foundation, either version 3 of the License, or (at your option)
any later version.

This program is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with this program. If not, see <https://www.gnu.org/licenses/>.
*)

theory LGPL_Ground_Critical_Pairs_Adapted_From_CeTA
  imports
    "HOL-Library.Sublist"
    Superposition_Calculus.Ground_Critical_Pairs
begin

text \<open>This theory is adapted from CeTA 2.44 (file
thys/Confluence_and_Completion/Critical_Pairs.thy).\<close>


lemma ballI2: "(\<And>x y. (x, y) \<in> A \<Longrightarrow> P x y) \<Longrightarrow> \<forall>(x, y) \<in> A. P x y"
  by auto

lemma ground_critical_pairs_fork:
  assumes cp: "(l, r) \<in> ground_critical_pairs R"
  shows "(l, r) \<in> (rewrite_inside_gctxt R)\<inverse> O rewrite_inside_gctxt R"
proof -
  from cp [unfolded ground_critical_pairs_def, simplified]
  obtain ctxt t t' where "l = ctxt\<langle>t'\<rangle>\<^sub>G" and "(ctxt\<langle>t\<rangle>\<^sub>G, r) \<in> R" and "(t, t') \<in> R"
    by metis

  have "(r, ctxt\<langle>t\<rangle>\<^sub>G) \<in> (rewrite_inside_gctxt R)\<inverse>"
    using \<open>(ctxt\<langle>t\<rangle>\<^sub>G, r) \<in> R\<close> subset_rewrite_inside_gctxt by blast
  moreover have "(ctxt\<langle>t\<rangle>\<^sub>G, l) \<in> rewrite_inside_gctxt R"
    using \<open>(t, t') \<in> R\<close> \<open>l = ctxt\<langle>t'\<rangle>\<^sub>G\<close> rewrite_inside_gctxt_def by fast
  ultimately show ?thesis by auto
qed

lemma ground_critical_pairs_complete:
  assumes
    cp: "(l, r) \<in> ground_critical_pairs R" and
    no_join: "(l, r) \<notin> (rewrite_inside_gctxt R)\<^sup>\<down>"
  shows "\<not> WCR (rewrite_inside_gctxt R)"
proof (rule notI)
  assume wcr: "WCR (rewrite_inside_gctxt R)"
  moreover from ground_critical_pairs_fork[OF cp] obtain u where
    ul: "(u, l) \<in> rewrite_inside_gctxt R" and ur: "(u, r) \<in> rewrite_inside_gctxt R"
    by auto
  ultimately show False
    using no_join
    unfolding WCR_on_def
    by simp
qed

lemma rewrite_inside_gctxt_closed_ctxt:
  assumes "(s, t) \<in> (rewrite_inside_gctxt R)\<^sup>*"
  shows "(C\<langle>s\<rangle>\<^sub>G, C\<langle>t\<rangle>\<^sub>G) \<in> (rewrite_inside_gctxt R)\<^sup>*"
proof -
  from assms obtain n where "(s,t) \<in> (rewrite_inside_gctxt R)^^n"
    using rtrancl_is_UN_relpow by auto
  then show ?thesis
  proof (induct n arbitrary: s)
    case 0 then show ?case by auto
  next
    case (Suc n)
    from relpow_Suc_D2[OF \<open>(s,t) \<in> (rewrite_inside_gctxt R)^^Suc n\<close>] obtain u where
      "(s,u) \<in> (rewrite_inside_gctxt R)" and "(u,t) \<in> (rewrite_inside_gctxt R)^^n"
      by auto
    from \<open>(s,u) \<in> (rewrite_inside_gctxt R)\<close> have "(C\<langle>s\<rangle>\<^sub>G, C\<langle>u\<rangle>\<^sub>G) \<in> (rewrite_inside_gctxt R)"
      apply (simp add: rewrite_inside_gctxt_def)
      using ctxt_ctxt by blast
    from Suc \<open>(u,t) \<in> (rewrite_inside_gctxt R)^^n\<close> have "(C\<langle>u\<rangle>\<^sub>G,C\<langle>t\<rangle>\<^sub>G) \<in> (rewrite_inside_gctxt R)\<^sup>*"
      by simp
    with \<open>(C\<langle>s\<rangle>\<^sub>G,C\<langle>u\<rangle>\<^sub>G) \<in> (rewrite_inside_gctxt R)\<close> show ?case
      by auto
  qed
qed

abbreviation (input) "greplace_at t p s \<equiv> (gctxt_at_pos t p)\<langle>s\<rangle>\<^sub>G"

lemma position_less_eq_eq_prefix: "position_less_eq = prefix"
  by (intro ext) (metis position_less_eq_def prefix_def)

lemma position_less_eq_strict_prefix: "position_less xs ys \<longleftrightarrow> strict_prefix xs ys"
  by (metis position_less_eq_def strict_prefix_def prefix_def)

lemma "position_par xs ys \<longleftrightarrow> \<not> prefix xs ys \<and> \<not> prefix ys xs"
  unfolding position_par_def
  unfolding position_less_eq_eq_prefix
  by metis

find_theorems "\<not> prefix ?ys ?xs \<and> \<not> prefix ?xs ?ys"

lemma parallel_gsubt_at_greplace_at:
  fixes p1 :: pos
  assumes parallel: "Sublist.parallel p1 p2"
    and p1: "p1 \<in> gposs t"
    and p2: "p2 \<in> gposs t"
  shows "gsubt_at (greplace_at t p1 s1) p2 = gsubt_at t p2"
  using assms
proof -
  from parallel_decomp[OF parallel]
  obtain p i j q1 q2 where p1_id: "p1 = p @ i # q1" and p2_id: "p2 = p @ j # q2"
    and ij: "i \<noteq> j" by blast
  from p1 p2 show ?thesis unfolding p1_id p2_id
  proof (induction p arbitrary: t)
    case (Cons k p)
    from Cons(3) obtain f ts where t: "t = GFun f ts" and k: "k < length ts" by (cases t, auto)
    note Cons = Cons[unfolded t]
    let ?p1 = "p @ i # q1" let ?p2 = "p @ j # q2"
    from Cons(2) Cons(3) have "?p1 \<in> gposs (ts ! k)" "?p2 \<in> gposs (ts ! k)" by auto
    from Cons(1)[OF this] have rec:
      "gsubt_at (greplace_at (ts ! k) ?p1 s1) ?p2 = gsubt_at (ts ! k) ?p2" .
    from k have min: "min (length ts) k = k" by simp
    show ?case unfolding t using rec min k
      by (simp add: nth_append)
  next
    case Nil
    from Nil(2) obtain f ts where t: "t = GFun f ts" and j: "j < length ts" by (cases t, auto)
    note Nil = Nil[unfolded t]
    from Nil have i: "i < length ts" by auto
    let ?p1 = "i # q1"
    let ?p2 = "j # q2"
    let ?s1 = "greplace_at (ts ! i) q1 s1"
    let ?ts1 = "ts[i := ?s1]"
    from j have j': "j < length ?ts1" by simp
    have "gsubt_at (greplace_at t ?p1 s1) ?p2 = gsubt_at (GFun f ?ts1) ?p2"
      unfolding t upd_conv_take_nth_drop[OF i] by simp
    also have "... = gsubt_at (ts ! j) q2" using ij by simp
    finally show ?case unfolding t by simp
  qed
qed

lemma gparallel_greplace_at:
  fixes p1 :: pos
  assumes parallel: "Sublist.parallel p1 p2"
    and p1: "p1 \<in> gposs t"
    and p2: "p2 \<in> gposs t"
  shows "greplace_at (greplace_at t p1 s1) p2 s2 = greplace_at (greplace_at t p2 s2) p1 s1"
proof -
  from parallel_decomp[OF parallel]
  obtain p i j q1 q2 where p1_id: "p1 = p @ i # q1" and p2_id: "p2 = p @ j # q2"
    and ij: "i \<noteq> j" by blast
  from p1 p2 show ?thesis unfolding p1_id p2_id
  proof (induction p arbitrary: t)
    case (Cons k p)
    from Cons(3) obtain f ts where t: "t = GFun f ts" and k: "k < length ts" by (cases t, auto)
    note Cons = Cons[unfolded t]
    let ?p1 = "p @ i # q1" let ?p2 = "p @ j # q2"
    from Cons(2) Cons(3) have "?p1 \<in> gposs (ts ! k)" "?p2 \<in> gposs (ts ! k)" by auto
    from Cons(1)[OF this] have rec: "
      greplace_at (greplace_at (ts ! k) ?p1 s1) ?p2 s2 =
      greplace_at (greplace_at (ts ! k) ?p2 s2) ?p1 s1" .
    from k have min: "min (length ts) k = k" by simp
    show ?case unfolding t using rec min k
      by (simp add: nth_append)
  next
    case Nil
    from Nil(2) obtain f ts where t: "t = GFun f ts" and j: "j < length ts" by (cases t, auto)
    note Nil = Nil[unfolded t]
    from Nil have i: "i < length ts" by auto
    let ?p1 = "i # q1"
    let ?p2 = "j # q2"
    let ?s1 = "greplace_at (ts ! i) q1 s1"
    let ?s2 = "greplace_at (ts ! j) q2 s2"
    let ?ts1 = "ts[i := ?s1]"
    let ?ts2 = "ts[j := ?s2]"
    from j have j': "j < length ?ts1" by simp
    from i have i': "i < length ?ts2" by simp
    have "greplace_at (greplace_at t ?p1 s1) ?p2 s2 = greplace_at (GFun f ?ts1) ?p2 s2"
      unfolding t upd_conv_take_nth_drop[OF i] by simp
    also have "... = GFun f (?ts1[j := ?s2])"
      unfolding upd_conv_take_nth_drop[OF j'] using ij by simp
    also have "... = GFun f (?ts2[i := ?s1])"
      using list_update_swap[OF ij] by simp
    also have "... = greplace_at (GFun f ?ts2) ?p1 s1"
      unfolding upd_conv_take_nth_drop[OF i'] using ij by simp
    also have "... = greplace_at (greplace_at t ?p2 s2) ?p1 s1"
      unfolding t upd_conv_take_nth_drop[OF j] by simp
    finally show ?case by simp
  qed
qed

lemma critical_pairs_main:
  fixes R :: "'f gterm rel"
  assumes
    st1: "(s, t1) \<in> rewrite_inside_gctxt R" and
    st2: "(s, t2) \<in> rewrite_inside_gctxt R"
  shows "(t1, t2) \<in> join (rewrite_inside_gctxt R) \<or>
    (\<exists>ctxt t1' t2'. t1 = ctxt\<langle>t1'\<rangle>\<^sub>G \<and> t2 = ctxt\<langle>t2'\<rangle>\<^sub>G \<and>
      ((t1', t2') \<in> ground_critical_pairs R \<or> (t2', t1') \<in> ground_critical_pairs R))"
proof -
  let ?R = "rewrite_inside_gctxt R"
  let ?CP = "ground_critical_pairs R"
  from st1 obtain C1 l1 r1 where
    lr1: "(l1, r1) \<in> R" and s1: "s = C1\<langle>l1\<rangle>\<^sub>G" and t1: "t1 = C1\<langle>r1\<rangle>\<^sub>G"
    by (auto simp: rewrite_inside_gctxt_def)
  from st2 obtain C2 l2 r2 where
    lr2: "(l2, r2) \<in> R" and s2: "s = C2\<langle>l2\<rangle>\<^sub>G" and t2: "t2 = C2\<langle>r2\<rangle>\<^sub>G"
    by (auto simp: rewrite_inside_gctxt_def)
  from s1 s2 have id: "C1\<langle>l1\<rangle>\<^sub>G = C2\<langle>l2\<rangle>\<^sub>G"
    by simp
  let ?q = "\<lambda>s t. (s, t) \<in> join ?R \<or> (\<exists>C l r. s = C\<langle>l\<rangle>\<^sub>G \<and> t = C\<langle>r\<rangle>\<^sub>G \<and> ((l, r) \<in> ?CP \<or> (r, l) \<in> ?CP))"
  let ?p = "\<lambda>(C1, C2). \<forall>l1 r1 l2 r2.
    (l1, r1) \<in> R \<longrightarrow> (l2, r2) \<in> R \<longrightarrow> (C1\<langle>l1\<rangle>\<^sub>G = C2\<langle>l2\<rangle>\<^sub>G) \<longrightarrow> ?q C1\<langle>r1\<rangle>\<^sub>G C2\<langle>r2\<rangle>\<^sub>G"
  have "?p C12" for C12 :: "'f gctxt \<times> 'f gctxt"
  proof -
    let ?m = "[\<lambda>(C1, C2). size C1 + size C2, \<lambda> (C1, C2). size C1]"
    show "?p C12"
    proof (induct rule: wf_induct [OF wf_measures [of ?m], of ?p])
      case (1 C12)
      obtain C1 C2 where C12: "C12 = (C1, C2)" by force
      show "?p C12" unfolding C12 split
      proof (intro allI impI)
        fix l1 r1 l2 r2
        assume lr1: "(l1, r1) \<in> R" and lr2: "(l2, r2) \<in> R" and id: "C1\<langle>l1\<rangle>\<^sub>G = C2\<langle>l2\<rangle>\<^sub>G"
        show "?q (C1\<langle>r1\<rangle>\<^sub>G) (C2\<langle>r2\<rangle>\<^sub>G)"
        proof (cases C1)
          case GHole note C1 = this
          with id have id: "l1 = C2\<langle>l2\<rangle>\<^sub>G" by simp
          let ?p = "ghole_pos C2"
          show ?thesis
          proof (cases "?p \<in> gposs l1")
            case True
            then have p: "?p \<in> gposs l1" by auto
            from gctxt_of_gpos_gterm_gsubt_at_to_gterm [OF p] obtain D where
              Dl1: "D\<langle>gsubt_at l1 ?p\<rangle>\<^sub>G = l1" and
              D: "D = gctxt_at_pos l1 (ghole_pos C2)" by blast
            from arg_cong [OF Dl1, of "\<lambda>t. t"]
            have "(D)\<langle>gsubt_at l1 ?p\<rangle>\<^sub>G = C2\<langle>l2\<rangle>\<^sub>G" unfolding id by simp
            from arg_cong [OF this, of "\<lambda> t. gsubt_at t ?p"]
            have "l2 = gsubt_at D\<langle>gsubt_at l1 ?p\<rangle>\<^sub>G ?p" by simp
            also have "... = gsubt_at D\<langle>gsubt_at l1 ?p\<rangle>\<^sub>G (ghole_pos D)"
              by (metis Dl1 gsubt_at_gctxt_apply_ghole)
            also have "... = gsubt_at l1 ?p"
              by (metis gsubt_at_gctxt_apply_ghole)
            finally have ident: "l2 = gsubt_at l1 ?p" by auto
            have in_cp: "((D)\<langle>r2\<rangle>\<^sub>G, r1) \<in> ground_critical_pairs R"
              unfolding ground_critical_pairs_def mem_Collect_eq
              by (metis Dl1 ident lr1 lr2)
            have pD: "?p = ghole_pos D"
              by (simp add: D p)
            from id have C2: "C2 = gctxt_at_pos l1 ?p" by simp
            have "C2\<langle>r2\<rangle>\<^sub>G = (gctxt_at_pos l1 ?p)\<langle>r2\<rangle>\<^sub>G" using C2 by simp
            also have "... = (D)\<langle>r2\<rangle>\<^sub>G" unfolding D ..
            finally have C2r\<sigma>: "C2\<langle>r2\<rangle>\<^sub>G = D\<langle>r2\<rangle>\<^sub>G" .
            from C1 have C1r\<sigma>: "C1\<langle>r1\<rangle>\<^sub>G = r1" by simp
            show ?thesis unfolding C2r\<sigma> C1r\<sigma>
            proof (rule disjI2, intro exI, intro conjI)
              show "r1 = \<box>\<^sub>G\<langle>r1\<rangle>\<^sub>G" by simp
            qed (insert in_cp, auto)
          next
            case False
            hence False
              using ghole_pos_in_apply id by blast
            thus ?thesis ..
          qed
        next
          case (GMore f1 bef1 D1 aft1) note C1 = this
          show ?thesis
          proof (cases C2)
            case GHole note C2 = this
            from C1 C2 have "((C2, C1), C12) \<in> measures ?m" unfolding C12 by auto
            from 1[rule_format, OF this, unfolded prod.case, rule_format, OF lr2 lr1 id[symmetric]]
            show ?thesis
            proof
              assume "(C2\<langle>r2\<rangle>\<^sub>G, C1\<langle>r1\<rangle>\<^sub>G) \<in> join ?R"
              then show ?thesis by auto
            qed blast
          next
            case (GMore f2 bef2 D2 aft2) note C2 = this
            let ?n1 = "length bef1"
            let ?n2 = "length bef2"
            note id = id [unfolded C1 C2]
            from id have f: "f1 = f2" by simp
            show ?thesis
            proof (cases "?n1 = ?n2")
              case True
              with id have idb: "bef1 = bef2" and ida: "aft1 = aft2"
                and idD: "D1\<langle>l1\<rangle>\<^sub>G = D2\<langle>l2\<rangle>\<^sub>G" by auto
              let ?C = "GMore f2 bef2 \<box>\<^sub>G aft2"
              have id1: "C1 = ?C \<circ>\<^sub>G\<^sub>c D1" unfolding C1 f ida idb by simp
              have id2: "C2 = ?C \<circ>\<^sub>G\<^sub>c D2" unfolding C2 by simp
              have "((D1, D2), C12) \<in> measures ?m" unfolding C12 C1 C2
                by auto
              from 1 [rule_format, OF this, unfolded split, rule_format,
                OF lr1 lr2 idD] have "?q D1\<langle>r1\<rangle>\<^sub>G D2\<langle>r2\<rangle>\<^sub>G" by auto
              then show ?thesis
              proof
                assume "(D1\<langle>r1\<rangle>\<^sub>G, D2\<langle>r2\<rangle>\<^sub>G) \<in> join ?R"
                then obtain s' where
                  seq1: "(D1\<langle>r1\<rangle>\<^sub>G, s') \<in> ?R^*" and
                  seq2: "(D2\<langle>r2\<rangle>\<^sub>G, s') \<in> ?R^*"
                  by auto
                from rewrite_inside_gctxt_closed_ctxt[OF seq1, of ?C]
                have seq1: "(C1\<langle>r1\<rangle>\<^sub>G, ?C\<langle>s'\<rangle>\<^sub>G) \<in> ?R^*" unfolding id1 by simp
                from rewrite_inside_gctxt_closed_ctxt[OF seq2, of ?C]
                have seq2: "(C2\<langle>r2\<rangle>\<^sub>G, ?C\<langle>s'\<rangle>\<^sub>G) \<in> ?R^*" using id2 by simp
                from seq1 seq2 show ?thesis by auto
              next
                assume "\<exists>C l r. D1\<langle>r1\<rangle>\<^sub>G = C\<langle>l\<rangle>\<^sub>G \<and> D2\<langle>r2\<rangle>\<^sub>G = C\<langle>r\<rangle>\<^sub>G \<and> ((l, r) \<in> ?CP \<or> (r, l) \<in> ?CP)"
                then obtain C l r where
                  idD: "D1\<langle>r1\<rangle>\<^sub>G = C\<langle>l\<rangle>\<^sub>G" "D2\<langle>r2\<rangle>\<^sub>G = C\<langle>r\<rangle>\<^sub>G" and mem: "((l, r) \<in> ?CP \<or> (r, l) \<in> ?CP)"
                  by blast
                show ?thesis
                  by (rule disjI2, unfold id1 id2, rule exI [of _ "?C \<circ>\<^sub>G\<^sub>c C"], intro exI, rule conjI [OF _ conjI [OF _ mem]], insert idD, auto)
              qed
            next
              case False
              let ?p1 = "?n1 # ghole_pos D1"
              let ?p2 = "?n2 # ghole_pos D2"
              have l2: "gsubt_at C1\<langle>l1\<rangle>\<^sub>G ?p2 = l2" unfolding C1 id by simp
              have p12: "Sublist.parallel ?p1 ?p2"
                using False by (simp add: Cons_parallelI1)
              have p1: "?p1 \<in> gposs C1\<langle>l1\<rangle>\<^sub>G"
                by (simp add: C1 ghole_pos_in_apply)
              have p2: "?p2 \<in> gposs C1\<langle>l1\<rangle>\<^sub>G"
                using C1 ghole_pos_in_apply id by auto
              let ?one = "greplace_at C1\<langle>l1\<rangle>\<^sub>G ?p1 r1"
              have one: "C1\<langle>r1\<rangle>\<^sub>G = ?one" unfolding C1 by simp
              have "(?one, greplace_at ?one ?p2 r2) \<in> rewrite_inside_gctxt R"
                unfolding rewrite_inside_gctxt_def mem_Collect_eq
                using l2 lr2 p1 p2
                using parallel_gsubt_at_greplace_at[OF p12 p1 p2]
                by (metis False gctxt_of_gpos_gterm_gsubt_at_to_gterm gposs_gctxt_at_pos_not_after
                    position_less_eq_Cons)
              then have one: "(C1\<langle>r1\<rangle>\<^sub>G, greplace_at ?one ?p2 r2) \<in> (rewrite_inside_gctxt R)^*"
                unfolding one by simp
              have l1: "gsubt_at C2\<langle>l2\<rangle>\<^sub>G ?p1 = l1" unfolding C2 id [symmetric] by simp
              have p21: "Sublist.parallel ?p2 ?p1" using False by auto
              have p1': "?p1 \<in> gposs (C2\<langle>l2\<rangle>\<^sub>G)"
                unfolding C2 id[symmetric]
                using C1 p1 by metis
              have p2': "?p2 \<in> gposs (C2\<langle>l2\<rangle>\<^sub>G)"
                unfolding C2
                using C1 id p2 by metis
              let ?two = "greplace_at (C2\<langle>l2\<rangle>\<^sub>G) ?p2 (r2)"
              have two: "C2\<langle>r2\<rangle>\<^sub>G = ?two" unfolding C2 by simp
              have "(?two, greplace_at ?two ?p1 r1) \<in> rewrite_inside_gctxt R"
                unfolding rewrite_inside_gctxt_def mem_Collect_eq
                by (metis C1 False GMore gctxt_of_gpos_gterm_gsubt_at_to_gterm
                    gposs_gctxt_at_pos_not_after id l1 lr1 p1' p2 p21 parallel_gsubt_at_greplace_at
                    position_less_eq_Cons)
              then have two: "(C2\<langle>r2\<rangle>\<^sub>G, greplace_at ?two ?p1 r1) \<in> (rewrite_inside_gctxt R)^*"
                unfolding two by simp
              have "greplace_at ?one ?p2 r2 = greplace_at (greplace_at C1\<langle>l1\<rangle>\<^sub>G ?p2 r2) ?p1 r1"
                by (rule gparallel_greplace_at[OF p12 p1 p2])
              also have "... = greplace_at ?two ?p1 r1" unfolding C1 C2 id ..
              finally have one_two: "greplace_at ?one ?p2 r2 = greplace_at ?two ?p1 r1" .
              have "(C1\<langle>r1\<rangle>\<^sub>G, C2\<langle>r2\<rangle>\<^sub>G) \<in> (rewrite_inside_gctxt R)\<^sup>\<down>"
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
  fixes R :: "'f gterm rel"
  assumes cp: "\<And> l r. (l, r) \<in> ground_critical_pairs R \<Longrightarrow> l \<noteq> r \<Longrightarrow>
    \<exists>s. (l, s) \<in> (rewrite_inside_gctxt R)\<^sup>* \<and> (r, s) \<in> (rewrite_inside_gctxt R)\<^sup>*"
  shows "WCR (rewrite_inside_gctxt R)"
proof (rule WCR_onI)
  let ?R = "rewrite_inside_gctxt R"
  let ?CP = "ground_critical_pairs R"
  fix s t1 t2
  assume steps: "(s, t1) \<in> ?R" "(s, t2) \<in> ?R"
  let ?p = "\<lambda> s'. (t1, s') \<in> ?R^* \<and> (t2, s') \<in> ?R^*"
  from critical_pairs_main [OF steps]
  have "\<exists> s'. ?p s'"
  proof (elim disjE)
    assume "\<exists>ctxt l r. t1 = ctxt\<langle>l\<rangle>\<^sub>G \<and> t2 = ctxt\<langle>r\<rangle>\<^sub>G \<and> ((l, r) \<in> ?CP \<or> (r, l) \<in> ?CP)"
    then obtain C l r where id: "t1 = C\<langle>l\<rangle>\<^sub>G" "t2 = C\<langle>r\<rangle>\<^sub>G"
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
          using cp[OF mem False] id rewrite_inside_gctxt_closed_ctxt by blast
      next
        assume mem: "(r, l) \<in> ?CP"
        show "\<exists> s'. ?p s'"
          using cp[OF mem] id rewrite_inside_gctxt_closed_ctxt by blast
      qed
    qed
  qed auto
  thus "(t1, t2) \<in> join ?R" by auto
qed

theorem ground_critical_pair_theorem:
  fixes R :: "'f gterm rel"
  shows "ground_critical_pair_theorem R"
proof (intro iffI)
  assume "WCR (rewrite_inside_gctxt R)"
  thus "ground_critical_pairs R \<subseteq> (rewrite_inside_gctxt R)\<^sup>\<down>"
    using ground_critical_pairs_complete
    by (metis subrelI)
next
  assume all_cp_joinable: "ground_critical_pairs R \<subseteq> (rewrite_inside_gctxt R)\<^sup>\<down>"
  show "WCR (rewrite_inside_gctxt R)"
  proof (rule critical_pairs)
    fix s t
    assume "(s, t) \<in> ground_critical_pairs R"
    with all_cp_joinable have "(s, t) \<in> join (rewrite_inside_gctxt R)" by auto
    then obtain u where s: "(s, u) \<in> (rewrite_inside_gctxt R)^*"
      and t: "(t, u) \<in> (rewrite_inside_gctxt R)^*" by auto
    thus "\<exists>u. (s, u) \<in> (rewrite_inside_gctxt R)^* \<and> (t, u) \<in> (rewrite_inside_gctxt R)^*"
      by metis
  qed
qed

end
