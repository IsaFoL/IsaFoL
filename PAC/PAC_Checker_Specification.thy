theory PAC_Checker_Specification
  imports PAC_Specification
     Refine_Imperative_HOL.IICF
     Weidenbach_Book_Base.WB_List_More

begin


datatype 'a status =
  is_failed: FAILED (status_error: 'a) |
  is_success: SUCCESS |
  is_found: FOUND

lemma is_success_alt_def:
  \<open>is_success a \<longleftrightarrow> a = SUCCESS\<close>
  by (cases a) auto

datatype 'a pac_step =
  AddD (pac_src1: nat) (pac_src2: nat) (new_id: nat) (pac_res: 'a) |
  Add (pac_src1: nat) (pac_src2: nat) (new_id: nat) (pac_res: 'a) |
  MultD (pac_src1: nat) (pac_mult: 'a) (new_id: nat) (pac_res: 'a) |
  Mult (pac_src1: nat) (pac_mult: 'a) (new_id: nat) (pac_res: 'a)


definition PAC_checker_specification
  :: \<open>int_poly multiset \<Rightarrow> int_poly \<Rightarrow> ('a status \<times> int_poly multiset) nres\<close>
where
  \<open>PAC_checker_specification A spec = SPEC(\<lambda>(b, B).
      (\<not>is_failed b \<longrightarrow> ideal (set_mset B) \<subseteq> ideal (set_mset A)) \<and>
      (is_found b \<longrightarrow> spec \<in> ideal (set_mset A)))\<close>

definition PAC_checker_specification_spec
  ::  \<open>int_poly \<Rightarrow> int_poly multiset \<Rightarrow> ('a status \<times> int_poly multiset) \<Rightarrow> bool\<close>
where
  \<open>PAC_checker_specification_spec spec A = (\<lambda>(b, B).
       (is_success b \<longrightarrow> PAC_Format\<^sup>*\<^sup>* A B) \<and>
       (is_found b \<longrightarrow> PAC_Format\<^sup>*\<^sup>* A B \<and> spec \<in> pac_ideal (set_mset A)))\<close>

abbreviation PAC_checker_specification2
  ::  \<open>int_poly \<Rightarrow> int_poly multiset \<Rightarrow> ('a status \<times> int_poly multiset) nres\<close>
where
  \<open>PAC_checker_specification2 spec A \<equiv> SPEC(PAC_checker_specification_spec spec A)\<close>

definition normalize_poly_spec :: \<open>_\<close> where
  \<open>normalize_poly_spec p = SPEC (\<lambda>r. p - r \<in> ideal polynom_bool)\<close>

lemma normalize_poly_spec_alt_def:
  \<open>normalize_poly_spec p = SPEC (\<lambda>r. r - p \<in> ideal polynom_bool)\<close>
  unfolding normalize_poly_spec_def
  by (auto dest: ideal.span_neg)

definition mult_poly_spec :: \<open>int mpoly \<Rightarrow> int mpoly \<Rightarrow> int mpoly nres\<close> where
  \<open>mult_poly_spec p q = SPEC (\<lambda>r. p * q - r \<in> ideal polynom_bool)\<close>

definition check_add :: \<open>(nat, int mpoly) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int mpoly \<Rightarrow> bool nres\<close> where
  \<open>check_add A p q i r =
     SPEC(\<lambda>b. b \<longrightarrow> p \<in># dom_m A \<and> q \<in># dom_m A \<and> i \<notin># dom_m A \<and>
            the (fmlookup A p) + the (fmlookup A q) - r \<in>  ideal polynom_bool)\<close>

definition check_mult :: \<open>(nat, int mpoly) fmap \<Rightarrow> nat \<Rightarrow> int mpoly \<Rightarrow> nat \<Rightarrow> int mpoly \<Rightarrow> bool nres\<close> where
  \<open>check_mult A p q i r =
     SPEC(\<lambda>b. b \<longrightarrow> p \<in># dom_m A \<and>i \<notin># dom_m A \<and>
            the (fmlookup A p) * q - r \<in>  ideal polynom_bool)\<close>

fun merge_status where
  \<open>merge_status (FAILED a) _ = FAILED a\<close> |
  \<open>merge_status _ (FAILED a) = FAILED a\<close> |
  \<open>merge_status FOUND _ = FOUND\<close> |
  \<open>merge_status _ FOUND = FOUND\<close> |
  \<open>merge_status _ _ = SUCCESS\<close>

definition PAC_checker_step
  ::  \<open>int_poly \<Rightarrow> unit status \<times> (nat, int_poly) fmap \<Rightarrow> int_poly pac_step \<Rightarrow>
    (unit status \<times> (nat, int_poly) fmap) nres\<close>
where
  \<open>PAC_checker_step = (\<lambda>spec (stat, A) st. case st of
     AddD _ _ _ _ \<Rightarrow>
       do {
        r \<leftarrow> normalize_poly_spec (pac_res st);
        eq \<leftarrow> check_add A (pac_src1 st) (pac_src2 st) (new_id st) r;
        st' \<leftarrow> SPEC(\<lambda>st'. \<not>is_failed st' \<and> (is_found st' \<longrightarrow> r - spec \<in> ideal polynom_bool));
        if eq
        then RETURN (merge_status stat st',
          fmupd (new_id st) r
            (fmdrop (pac_src1 st) (fmdrop (pac_src2 st) A)))
        else RETURN (FAILED (), A)
   }
   | Add _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly_spec (pac_res st);
        eq \<leftarrow> check_add A (pac_src1 st) (pac_src2 st) (new_id st) r;
        st' \<leftarrow> SPEC(\<lambda>st'. is_success st' \<or> (is_found st' \<longrightarrow> r - spec \<in> ideal polynom_bool));
        if eq
        then RETURN (merge_status stat st',
          fmupd (new_id st) r A)
        else RETURN (FAILED (), A)
   }
   | MultD _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly_spec (pac_res st);
         q \<leftarrow> normalize_poly_spec (pac_mult st);
        eq \<leftarrow> check_mult A (pac_src1 st) q (new_id st) r;
        st' \<leftarrow> SPEC(\<lambda>st'. is_success st' \<or> (is_found st' \<longrightarrow> r - spec \<in> ideal polynom_bool));
        if eq
        then RETURN (merge_status stat st',
          fmupd (new_id st) r
            (fmdrop (pac_src1 st) A))
        else RETURN (FAILED (), A)
   }
   | Mult _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly_spec (pac_res st);
         q \<leftarrow> normalize_poly_spec (pac_mult st);
        eq \<leftarrow> check_mult A (pac_src1 st) q (new_id st) r;
        st' \<leftarrow> SPEC(\<lambda>st'. is_success st' \<or> (is_found st' \<longrightarrow> r - spec \<in> ideal polynom_bool));
        if eq
        then RETURN (merge_status stat st',
          fmupd (new_id st) r A)
        else RETURN (FAILED (), A)
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


definition status_rel where
  \<open>status_rel = {(SUCCESS, SUCCESS), (FOUND, FOUND)} \<union>
    (\<lambda>(a, b). (FAILED a, FAILED b)) ` (UNIV \<times> UNIV)\<close>

lemma status_rel_intro[iff,simp]:
  \<open>(FAILED a, FAILED b) \<in> status_rel\<close>
  \<open>(SUCCESS,SUCCESS) \<in> status_rel\<close>
  \<open>(FOUND,FOUND) \<in> status_rel\<close>
  \<open>(FAILED a, SUCCESS) \<notin> status_rel\<close>
  \<open>(FAILED a, FOUND) \<notin> status_rel\<close>
  \<open>(SUCCESS,FAILED a) \<notin> status_rel\<close>
  \<open>(SUCCESS,FOUND) \<notin> status_rel\<close>
  \<open>(FOUND,SUCCESS) \<notin> status_rel\<close>
  \<open>(FOUND,FAILED a) \<notin> status_rel\<close>
  by (auto simp: status_rel_def)

lemma status_rel_alt_def:
  \<open>(a, b) \<in> status_rel \<longleftrightarrow>
     (is_failed a = is_failed b) \<and>
     (is_success a = is_success b) \<and>
     (is_found a = is_found b)\<close>
   by (cases a; cases b) auto

lemma is_merge_status[simp]:
  \<open>is_failed (merge_status a st') \<longleftrightarrow> is_failed a \<or> is_failed st'\<close>
  \<open>is_found (merge_status a st') \<longleftrightarrow> \<not>is_failed a \<and> \<not>is_failed st' \<and> (is_found a \<or> is_found st')\<close>
  \<open>is_success (merge_status a st') \<longleftrightarrow> (is_success a \<and> is_success st')\<close>
  by (cases a; cases st'; auto; fail)+

lemma status_rel_merge_status:
  \<open>(merge_status a b, SUCCESS) \<notin> status_rel \<longleftrightarrow>
    (\<exists>a'. a = FAILED a') \<or> (\<exists>a'. b = FAILED a') \<or>
    a = FOUND \<or> (b = FOUND)\<close>
  by (cases a; cases b; auto)

lemma Ex_status_iff:
  \<open>(\<exists>a. P a) \<longleftrightarrow> P SUCCESS \<or> P FOUND \<or> (\<exists>a. P (FAILED a))\<close>
  apply auto
  apply (case_tac a; auto)
  done

lemma is_failed_alt_def:
  \<open>is_failed st' \<longleftrightarrow> \<not>is_success st' \<and> \<not>is_found st'\<close>
  by (cases st') auto

lemma merge_status_eq_iff[simp]:
  \<open>merge_status a SUCCESS = SUCCESS \<longleftrightarrow> a = SUCCESS\<close>
  \<open>merge_status a SUCCESS = FOUND \<longleftrightarrow> a = FOUND\<close>
  \<open>merge_status SUCCESS a = SUCCESS \<longleftrightarrow> a = SUCCESS\<close>
  \<open>merge_status SUCCESS a = FOUND \<longleftrightarrow> a = FOUND\<close>
  \<open>merge_status SUCCESS a = FAILED b \<longleftrightarrow> a = FAILED b\<close>
  \<open>merge_status a SUCCESS = FAILED b \<longleftrightarrow> a = FAILED b\<close>
  \<open>merge_status FOUND a = FAILED b \<longleftrightarrow> a = FAILED b\<close>
  \<open>merge_status a FOUND = FAILED b \<longleftrightarrow> a = FAILED b\<close>
  \<open>merge_status a FOUND = SUCCESS \<longleftrightarrow> False\<close>
  by (cases a; auto; fail)+

find_theorems "is_success _ \<longleftrightarrow> _"
lemma PAC_checker_step_PAC_checker_specification2:
  fixes a :: \<open>unit status\<close>
  assumes [simp,intro]: \<open>(A,B) \<in> polys_rel\<close> and
    \<open>\<not>is_failed a\<close> and
    [simp,intro]: \<open>a = FOUND \<Longrightarrow> spec \<in> pac_ideal (set_mset B)\<close>
  shows \<open>PAC_checker_step spec (a, A) st \<le> \<Down> (status_rel \<times>\<^sub>r polys_rel) (PAC_checker_specification2 spec B)\<close>
proof -
  have H1: \<open> x12 \<in># dom_m A \<Longrightarrow>
       2 * the (fmlookup A x12) - r \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       r - spec \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       spec \<in> pac_ideal (set_mset B)\<close> for x12 r
     using \<open>(A,B) \<in> polys_rel\<close>
      ideal.span_add[OF ideal.span_add[OF ideal.span_neg ideal.span_neg,
         of \<open>the (fmlookup A x12)\<close> _  \<open>the (fmlookup A x12)\<close>],
      of \<open>set_mset B \<union> polynom_bool\<close> \<open>2 * the (fmlookup A x12) - r\<close>]
     unfolding polys_rel_def
    apply (subgoal_tac \<open>r \<in> pac_ideal (set_mset B)\<close>)
     apply (auto dest!: multi_member_split simp: ran_m_def)
     apply (metis Un_insert_left diff_in_polynom_bool_pac_idealI ideal.span_diff ideal.span_zero)
     by (metis (no_types, lifting) UnCI Un_insert_left diff_in_polynom_bool_pac_idealI ideal.span_add ideal.span_base mult_2 set_image_mset set_mset_add_mset_insert union_single_eq_member)

  have H2: \<open>x11 \<in># dom_m A \<Longrightarrow>
       x12 \<in># dom_m A \<Longrightarrow>
       the (fmlookup A x11) + the (fmlookup A x12) - r
       \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       r - spec \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       spec \<in> pac_ideal (set_mset B)\<close>  for x12 r x11
     using \<open>(A,B) \<in> polys_rel\<close>
      ideal.span_add[OF ideal.span_add[OF ideal.span_neg ideal.span_neg,
         of \<open>the (fmlookup A x11)\<close> _  \<open>the (fmlookup A x12)\<close>],
      of \<open>set_mset B \<union> polynom_bool\<close> \<open>the (fmlookup A x11) + the (fmlookup A x12) - r\<close>]
     unfolding polys_rel_def
    apply (subgoal_tac \<open>r \<in> pac_ideal (set_mset B)\<close>)
     apply (auto dest!: multi_member_split simp: ran_m_def ideal.span_base)
     apply (metis Un_insert_left diff_in_polynom_bool_pac_idealI ideal.span_diff ideal.span_zero)
     by (smt Un_insert_left diff_diff_eq2 diff_in_polynom_bool_pac_idealI diff_zero ideal.span_base ideal.span_diff ideal.span_neg insertI1 minus_diff_eq)

  have eq_successI: \<open>st' \<noteq> FAILED () \<Longrightarrow>
       st' \<noteq> FOUND \<Longrightarrow> st' = SUCCESS\<close> for st'
    by (cases st') auto
  have [iff]: \<open>a \<noteq> FAILED ()\<close> and
    [intro]: \<open>a \<noteq> SUCCESS \<Longrightarrow> a = FOUND\<close> and
    [simp]: \<open>merge_status a FOUND = FOUND\<close>
    using assms(2) by (cases a; auto)+
  note [[goals_limit=1]]
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
      apply (auto simp: Ex_status_iff)
      apply (rule RES_refine)
      apply (auto simp: Ex_status_iff)
      apply (rule RES_refine)
      apply (rule_tac x = \<open>(if a = SUCCESS then SUCCESS else FOUND,add_mset r B - (if x11 \<noteq> x12 then {#the (fmlookup A x11), the (fmlookup A x12)#} else {#the (fmlookup A x11)#}))\<close> in bexI)
      apply (auto simp: polys_rel_update_remove PAC_Format_add_and_remove
           status_rel_alt_def is_failed_def is_success_def is_found_def
        dest!: eq_successI
        split: if_splits)[2]
      apply (rule RES_refine)
      apply (auto simp: status_rel_alt_def Ex_status_iff)
      apply (rule RES_refine)
      apply (rule_tac x = \<open>(if a = FOUND \<or> st' = FOUND then FOUND else SUCCESS,add_mset r B - (if x11 \<noteq> x12 then {#the (fmlookup A x11), the (fmlookup A x12)#} else {#the (fmlookup A x11)#}))\<close> in bexI)
      apply (auto simp: polys_rel_update_remove PAC_Format_add_and_remove
           status_rel_alt_def is_failed_def is_success_def is_found_def H1 H2
        dest!: eq_successI
        split: if_splits)[2]
      apply (rule RES_refine)
      apply (auto simp: status_rel_alt_def Ex_status_iff)
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


definition PAC_checker
  :: \<open>int_poly \<Rightarrow> (nat, int_poly) fmap \<Rightarrow> int_poly pac_step list \<Rightarrow>
    (unit status \<times> (nat, int_poly) fmap) nres\<close>
where
  \<open>PAC_checker spec A st = do {
    (S, _) \<leftarrow> WHILE\<^sub>T
       (\<lambda>((b :: unit status, A :: (nat, int_poly) fmap), n::nat). \<not>is_failed b \<and> n < length st)
       (\<lambda>((bA), n). do {
          ASSERT(n < length st);
          S \<leftarrow> PAC_checker_step spec (bA) (st ! n);
          RETURN (S, (n+1))
        })
      ((SUCCESS, A), 0);
    RETURN S
  }\<close>


lemma PAC_checker_specification_spec_trans:
  \<open>PAC_checker_specification_spec spec A (st, x2) \<Longrightarrow>
    PAC_checker_specification_spec spec x2 (st, x1a) \<Longrightarrow>
    PAC_checker_specification_spec spec A (st, x1a)\<close>
 unfolding PAC_checker_specification_spec_def
 by auto

lemma RES_SPEC_eq:
  \<open>RES \<Phi> = SPEC(\<lambda>P. P \<in> \<Phi>)\<close>
  by auto

lemma PAC_checker_PAC_checker_specification2:
  \<open>(A, B) \<in> polys_rel \<Longrightarrow>
  PAC_checker spec A st \<le> \<Down> (status_rel \<times>\<^sub>r polys_rel) (PAC_checker_specification2 spec B)\<close>
  unfolding PAC_checker_def conc_fun_RES
  apply (subst RES_SPEC_eq)
  apply (refine_vcg WHILET_rule[where
      I = \<open>\<lambda>((bB), n). n \<le> length st \<and> bB \<in> (status_rel \<times>\<^sub>r polys_rel)\<inverse> ``
                      Collect (PAC_checker_specification_spec spec B)\<close>
    and R = \<open>measure (\<lambda>(_, n).  Suc (length st) - n)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal by (force simp: PAC_checker_specification_spec_def status_rel_def)
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

definition full_checker where
  \<open>full_checker A pac spec = do {
     A \<leftarrow> SPEC(\<lambda>A'. \<forall>i. fmlookup A i = fmlookup A' i);
     (b, A) \<leftarrow> PAC_checker A pac;
     SPEC(\<lambda>b'. b' \<longrightarrow> b \<and> spec \<in># ran_m A)
}\<close>


definition remap_polys :: \<open>(nat, int mpoly) fmap \<Rightarrow> (nat, int mpoly) fmap nres\<close> where
  \<open>remap_polys A = do{
    dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
   FOREACH dom
     (\<lambda>i A'.
        if i \<in># dom_m A
        then do {
          p \<leftarrow> SPEC(\<lambda>p. the (fmlookup A i) - p \<in> ideal polynom_bool);
          RETURN(fmupd i p A')
        } else RETURN A')
     fmempty
 }\<close>

lemma remap_polys_spec:
  \<open>remap_polys A \<le> SPEC(\<lambda>A'. dom_m A = dom_m A' \<and>
    (\<forall>i \<in># dom_m A. the (fmlookup A i) - the (fmlookup A' i) \<in> ideal polynom_bool))\<close>
    (is \<open>_ \<le> SPEC(?P)\<close>)
  unfolding remap_polys_def
  apply (refine_vcg FOREACH_rule[where
    I = \<open>\<lambda>dom A'.
      set_mset (dom_m A') =  set_mset (dom_m A) - dom \<and>
      (\<forall>i \<in> set_mset (dom_m A) - dom. the (fmlookup A i) - the (fmlookup A' i) \<in> ideal polynom_bool)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal
    by auto
  subgoal by auto
  subgoal using ideal.span_add by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: distinct_set_mset_eq_iff distinct_mset_dom)
  subgoal by auto
  done


definition full_checker_specification ::  \<open>int_poly multiset \<Rightarrow> int_poly \<Rightarrow> bool nres\<close> where
  \<open>full_checker_specification A spec = SPEC(\<lambda>b. b \<longrightarrow> spec \<in> pac_ideal (set_mset A))\<close>

lemma
  assumes \<open>(A, A') \<in> polys_rel\<close>
  shows
    \<open>full_checker A pac spec \<le> \<Down> bool_rel (full_checker_specification A' spec)\<close>
proof -

  show ?thesis
    unfolding full_checker_def full_checker_specification_def
    apply (refine_vcg PAC_checker_PAC_checker_specification2[THEN order_trans, of _ A'])
    subgoal
      using fmap_ext assms by (auto simp: polys_rel_def ran_m_def)
    subgoal
      by (auto simp add: PAC_checker_specification_spec_def conc_fun_RES polys_rel_def
        dest!: rtranclp_PAC_Format_subset_ideal)
    done
qed


end

