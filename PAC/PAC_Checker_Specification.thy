theory PAC_Checker_Specification
  imports PAC_Specification
     Refine_Imperative_HOL.IICF
     Weidenbach_Book_Base.WB_List_More

begin

datatype pac_step =
  AddD (pac_src1: nat) (pac_src2: nat) (new_id: nat) (pac_res: int_poly) |
  Add (pac_src1: nat) (pac_src2: nat) (new_id: nat) (pac_res: int_poly) |
  MultD (pac_src1: nat) (pac_mult: int_poly) (new_id: nat) (pac_res: int_poly) |
  Mult (pac_src1: nat) (pac_mult: int_poly) (new_id: nat) (pac_res: int_poly)


definition PAC_checker_specification ::  \<open>int_poly multiset \<Rightarrow> (bool \<times> int_poly multiset) nres\<close> where
  \<open>PAC_checker_specification A = SPEC(\<lambda>(b, B). b \<longrightarrow> ideal (set_mset B) \<subseteq> ideal (set_mset A))\<close>

definition PAC_checker_specification_spec ::  \<open>int_poly multiset \<Rightarrow> (bool \<times> int_poly multiset) \<Rightarrow> bool\<close> where
  \<open>PAC_checker_specification_spec A = (\<lambda>(b, B). b \<longrightarrow> PAC_Format\<^sup>*\<^sup>* (A) (B))\<close>

abbreviation PAC_checker_specification2 ::  \<open>int_poly multiset \<Rightarrow> (bool \<times> int_poly multiset) nres\<close> where
  \<open>PAC_checker_specification2 A \<equiv> SPEC(PAC_checker_specification_spec A)\<close>

definition normalize_poly_spec :: \<open>_\<close> where
  \<open>normalize_poly_spec p = SPEC (\<lambda>r. p - r \<in> ideal polynom_bool)\<close>

lemma normalize_poly_spec_alt_def:
  \<open>normalize_poly_spec p = SPEC (\<lambda>r. r - p \<in> ideal polynom_bool)\<close>
  unfolding normalize_poly_spec_def
  by (auto dest: ideal.span_neg)

definition mult_poly_spec :: \<open>_\<close> where
  \<open>mult_poly_spec p q = SPEC (\<lambda>r. p * q - r \<in> ideal polynom_bool)\<close>

definition check_add :: \<open>(nat, int mpoly) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int mpoly \<Rightarrow> bool nres\<close> where
  \<open>check_add A p q i r =
     SPEC(\<lambda>b. b \<longrightarrow> p \<in># dom_m A \<and> q \<in># dom_m A \<and> i \<notin># dom_m A \<and>
            the (fmlookup A p) + the (fmlookup A q) - r \<in>  ideal polynom_bool)\<close>

definition check_mult where
  \<open>check_mult A p q i r =
     SPEC(\<lambda>b. b \<longrightarrow> p \<in># dom_m A \<and>i \<notin># dom_m A \<and>
            the (fmlookup A p) * q - r \<in>  ideal polynom_bool)\<close>


definition PAC_checker_step ::  \<open>(nat, int_poly) fmap  \<Rightarrow> pac_step \<Rightarrow> (bool \<times> (nat, int_poly) fmap) nres\<close> where
  \<open>PAC_checker_step A st = (case st of
     AddD _ _ _ _ \<Rightarrow>
       do {
        r \<leftarrow> normalize_poly_spec (pac_res st);
        eq \<leftarrow> check_add A (pac_src1 st) (pac_src2 st) (new_id st) r;
        if eq
        then RETURN (True,
          fmupd (new_id st) r
            (fmdrop (pac_src1 st) (fmdrop (pac_src2 st) A)))
        else RETURN (False, A)
   }
   | Add _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly_spec (pac_res st);
        eq \<leftarrow> check_add A (pac_src1 st) (pac_src2 st) (new_id st) r;
        if eq
        then RETURN (True,
          fmupd (new_id st) r A)
        else RETURN (False, A)
   }
   | MultD _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly_spec (pac_res st);
        eq \<leftarrow> check_mult A (pac_src1 st) (pac_mult st) (new_id st) r;
        if eq
        then RETURN (True,
          fmupd (new_id st) r
            (fmdrop (pac_src1 st) A))
        else RETURN (False, A)
   }
   | Mult _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly_spec (pac_res st);
        eq \<leftarrow> check_mult A (pac_src1 st) (pac_mult st) (new_id st) r;
        if eq
        then RETURN (True,
          fmupd (new_id st) r A)
        else RETURN (False, A)
   }
 )\<close>

definition polys_rel :: \<open>_\<close> where
\<open>polys_rel = {(A, B). B = (ran_m A)}\<close>

lemma polys_rel_update_remove:
  \<open>x13 \<notin>#dom_m A \<Longrightarrow> x11 \<in># dom_m A \<Longrightarrow> x12 \<in># dom_m A \<Longrightarrow> x11 \<noteq> x12 \<Longrightarrow> (A,B) \<in> polys_rel \<Longrightarrow>
   (fmupd x13 r (fmdrop x11 (fmdrop x12 A)),
        add_mset r B - {#the (fmlookup A x11), the (fmlookup A x12)#})
       \<in> polys_rel\<close>
  \<open>x13 \<notin>#dom_m A \<Longrightarrow> x11 \<in># dom_m A \<Longrightarrow> (A,B) \<in> polys_rel \<Longrightarrow>
   (fmupd x13 r (fmdrop x11 A),add_mset r B - {#the (fmlookup A x11)#})
       \<in> polys_rel\<close>
  \<open>x13 \<notin>#dom_m A \<Longrightarrow> (A,B) \<in> polys_rel \<Longrightarrow>
   (fmupd x13 r A, add_mset r B) \<in> polys_rel\<close>
  using distinct_mset_dom[of A]
  apply (auto simp: polys_rel_def ran_m_mapsto_upd ran_m_mapsto_upd_notin
    ran_m_fmdrop)
  apply (subst ran_m_mapsto_upd_notin)
  apply (auto dest: in_diffD dest!: multi_member_split simp: ran_m_fmdrop ran_m_fmdrop_If distinct_mset_remove1_All ran_m_def
      add_mset_eq_add_mset removeAll_notin
    split: if_splits intro!: image_mset_cong)
    by (smt count_inI diff_single_trivial fmlookup_drop image_mset_cong2 replicate_mset_0)

lemma polys_rel_in_dom_inD:
  \<open>(A, B) \<in> polys_rel \<Longrightarrow>
    x12 \<in># dom_m A \<Longrightarrow>
    the (fmlookup A x12) \<in># B\<close>
  by (auto simp: polys_rel_def)

lemma PAC_Format_add_and_remove:
  \<open>r - x14 \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       (A, B) \<in> polys_rel \<Longrightarrow>
       x12 \<in># dom_m A \<Longrightarrow>
       x13 \<notin># dom_m A \<Longrightarrow>
       2 * the (fmlookup A x12) - r \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       PAC_Format\<^sup>*\<^sup>* B (remove1_mset (the (fmlookup A x12)) (add_mset r B))\<close>
   \<open>r - x14 \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       (A, B) \<in> polys_rel \<Longrightarrow>
       the (fmlookup A x11) + the (fmlookup A x12) - r \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       x11 \<in># dom_m A \<Longrightarrow>
       x12 \<in># dom_m A \<Longrightarrow>
       PAC_Format\<^sup>*\<^sup>* B (add_mset r B)\<close>
   \<open>r - x14 \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       (A, B) \<in> polys_rel \<Longrightarrow>
       x11 \<in># dom_m A \<Longrightarrow>
       x12 \<in># dom_m A \<Longrightarrow>
       the (fmlookup A x11) + the (fmlookup A x12) - r \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       x11 \<noteq> x12 \<Longrightarrow>
       PAC_Format\<^sup>*\<^sup>* B
        (add_mset r B - {#the (fmlookup A x11), the (fmlookup A x12)#})\<close>
   \<open>(A, B) \<in> polys_rel \<Longrightarrow>
       r - x34 \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       x11 \<in># dom_m A \<Longrightarrow>
       the (fmlookup A x11) * x32 - r \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       PAC_Format\<^sup>*\<^sup>* B (add_mset r B)\<close>
   \<open>(A, B) \<in> polys_rel \<Longrightarrow>
       r - x34 \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       x11 \<in># dom_m A \<Longrightarrow>
       the (fmlookup A x11) * x32 - r \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       PAC_Format\<^sup>*\<^sup>* B (remove1_mset (the (fmlookup A x11)) (add_mset r B))\<close>
   subgoal
     apply (rule converse_rtranclp_into_rtranclp)
     apply (rule PAC_Format.add[of \<open>the (fmlookup A x12)\<close> B \<open>the (fmlookup A x12)\<close>])
     apply (auto dest: polys_rel_in_dom_inD)
     apply (rule converse_rtranclp_into_rtranclp)
     apply (rule PAC_Format.del[of \<open>the (fmlookup A x12)\<close>])
     apply (auto dest: polys_rel_in_dom_inD)
     done
  subgoal H2
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule PAC_Format.add[of \<open>the (fmlookup A x11)\<close> B \<open>the (fmlookup A x12)\<close>])
    apply (auto dest: polys_rel_in_dom_inD)
    done
  subgoal
    apply (rule rtranclp_trans)
    apply (rule H2; assumption)
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule PAC_Format.del[of \<open>the (fmlookup A x12)\<close>])
    apply (auto dest: polys_rel_in_dom_inD)
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule PAC_Format.del[of \<open>the (fmlookup A x11)\<close>])
    apply (auto dest: polys_rel_in_dom_inD)
    apply (auto simp: polys_rel_def ran_m_def add_mset_eq_add_mset dest!: multi_member_split)
    done
 subgoal H2
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule PAC_Format.mult[of \<open>the (fmlookup A x11)\<close> B \<open>x32\<close>])
    apply (auto dest: polys_rel_in_dom_inD)
    done
  subgoal
    apply (rule rtranclp_trans)
    apply (rule H2; assumption)
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule PAC_Format.del[of \<open>the (fmlookup A x11)\<close>])
    apply (auto dest: polys_rel_in_dom_inD)
    done
  done

lemma PAC_checker_step_PAC_checker_specification2:
  assumes \<open>(A,B) \<in> polys_rel\<close>
  shows \<open>PAC_checker_step A st \<le> \<Down> (bool_rel \<times>\<^sub>r polys_rel) (PAC_checker_specification2 B)\<close>
proof -
  show ?thesis
    unfolding PAC_checker_step_def PAC_checker_specification_spec_def
      normalize_poly_spec_alt_def check_mult_def check_add_def
    apply (cases st)
    apply clarsimp_all
    subgoal for x11 x12 x13 x14
      apply refine_vcg
      using assms
      apply (auto 6 4 simp: RETURN_def 
        intro: PAC_Format.intros simp flip: insert_minus_eq)
      apply (rule RES_refine)
      apply auto
      defer
      apply (rule RES_refine)
      apply auto
      apply (rule RES_refine)
      apply (rule_tac x = \<open>(True, add_mset r B - (if x11 \<noteq> x12 then {#the (fmlookup A x11), the (fmlookup A x12)#} else {#the (fmlookup A x11)#}))\<close> in bexI)
      apply (auto simp: polys_rel_update_remove PAC_Format_add_and_remove)
      done
    subgoal
      apply refine_vcg
      using assms
      apply (auto 6 4 simp: RETURN_def 
        intro: PAC_Format.intros simp flip: insert_minus_eq)
      apply (rule RES_refine)
      apply auto
      defer
      apply (rule RES_refine)
      apply auto
      apply (rule RES_refine)
      apply (rule_tac x = \<open>(True, add_mset r B)\<close> in bexI)
      apply (auto simp: polys_rel_update_remove PAC_Format_add_and_remove)
      done
    subgoal for x11 x32 x33 x34
      using assms
      apply refine_vcg
      apply (auto 6 4 simp: RETURN_def
        intro: PAC_Format.intros simp flip: insert_minus_eq)
      apply (rule RES_refine)
      apply auto
      defer
      apply (rule RES_refine)
      apply auto
      apply (rule RES_refine)
      apply (rule_tac x = \<open>(True, add_mset r B - {#the (fmlookup A x11)#})\<close> in bexI)
      apply (auto simp: polys_rel_update_remove PAC_Format_add_and_remove)
      done
    subgoal for x11 x32 x33 x34
      using assms
      apply refine_vcg
      apply (auto 6 4 simp: RETURN_def
        intro: PAC_Format.intros simp flip: insert_minus_eq)
      apply (rule RES_refine)
      apply auto
      defer
      apply (rule RES_refine)
      apply auto
      apply (rule RES_refine)
      apply (rule_tac x = \<open>(True, add_mset r B)\<close> in bexI)
      apply (auto simp: polys_rel_update_remove PAC_Format_add_and_remove)
      done
  done
qed

definition PAC_checker:: \<open>(nat, int_poly) fmap \<Rightarrow> pac_step list \<Rightarrow> (bool \<times> (nat, int_poly) fmap) nres\<close> where
  \<open>PAC_checker A st = do {
    (S, _) \<leftarrow> WHILE\<^sub>T
       (\<lambda>((b, A), n::nat). b \<and> n < length st)
       (\<lambda>((b, A), n). do {
          ASSERT(n < length st);
          S \<leftarrow> PAC_checker_step A (st ! n);
          RETURN (S, (n+1))
        })
      ((True, A), 0);
    RETURN S
  }\<close>


lemma PAC_checker_specification_spec_trans:
  \<open>PAC_checker_specification_spec A (True, x2) \<Longrightarrow>
    PAC_checker_specification_spec x2 x1a \<Longrightarrow>
    PAC_checker_specification_spec A x1a\<close>
 unfolding PAC_checker_specification_spec_def
 by auto

lemma RES_SPEC_eq:
  \<open>RES \<Phi> = SPEC(\<lambda>P. P \<in> \<Phi>)\<close>
  by auto
lemma PAC_checker_PAC_checker_specification2:
  \<open>(A, B) \<in> polys_rel \<Longrightarrow> PAC_checker A st \<le> \<Down> (bool_rel \<times>\<^sub>r polys_rel) (PAC_checker_specification2 B)\<close>
  unfolding PAC_checker_def conc_fun_RES
  apply (subst RES_SPEC_eq)
  apply (refine_vcg WHILET_rule[where
      I = \<open>\<lambda>((bB), n). n \<le> length st \<and> bB \<in> (bool_rel \<times>\<^sub>r polys_rel)\<inverse> ``
                      Collect (PAC_checker_specification_spec B)\<close>
    and R = \<open>measure (\<lambda>(_, n).  Suc (length st) - n)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal by (force simp: PAC_checker_specification_spec_def)
  subgoal by auto
  subgoal
    apply auto
  apply (rule
     PAC_checker_step_PAC_checker_specification2[THEN order_trans])
     apply assumption
     apply (auto intro: PAC_checker_specification_spec_trans simp: conc_fun_RES)
     done
  subgoal
    by auto
  done

end