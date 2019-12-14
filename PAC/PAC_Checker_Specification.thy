theory PAC_Checker_Specification
  imports PAC_Specification
     Refine_Imperative_HOL.IICF
     Weidenbach_Book_Base.WB_List_More

begin


datatype status =
  is_failed: FAILED |
  is_success: SUCCESS |
  is_found: FOUND

lemma is_success_alt_def:
  \<open>is_success a \<longleftrightarrow> a = SUCCESS\<close>
  by (cases a) auto

datatype 'a pac_step =
  Add (pac_src1: nat) (pac_src2: nat) (new_id: nat) (pac_res: 'a) |
  Mult (pac_src1: nat) (pac_mult: 'a) (new_id: nat) (pac_res: 'a) |
  Extension (new_id: nat) (pac_res: 'a) |
  Del (pac_src1: nat)

type_synonym  pac_state = \<open>(nat set \<times> int_poly multiset)\<close>

definition PAC_checker_specification
  :: \<open>int_poly multiset \<Rightarrow> int_poly \<Rightarrow> (status \<times> nat set \<times> int_poly multiset) nres\<close>
where
  \<open>PAC_checker_specification A spec = SPEC(\<lambda>(b, \<V>, B).
      (\<not>is_failed b \<longrightarrow> restricted_ideal_to\<^sub>I (\<Union>(vars ` set_mset A) \<union> vars spec) B \<subseteq> restricted_ideal_to\<^sub>I (\<Union>(vars ` set_mset A) \<union> vars spec) A) \<and>
      (is_found b \<longrightarrow> spec \<in> pac_ideal (set_mset A)))\<close>

definition PAC_checker_specification_spec
  ::  \<open>int_poly \<Rightarrow> pac_state \<Rightarrow> (status \<times> pac_state) \<Rightarrow> bool\<close>
where
  \<open>PAC_checker_specification_spec spec = (\<lambda>(\<V>, A) (b, B). \<Union>(vars ` set_mset A) \<subseteq> \<V> \<and>
       (is_success b \<longrightarrow> PAC_Format\<^sup>*\<^sup>* (\<V>, A) B) \<and>
       (is_found b \<longrightarrow> PAC_Format\<^sup>*\<^sup>* (\<V>, A) B \<and> spec \<in> pac_ideal (set_mset A)))\<close>

abbreviation PAC_checker_specification2
  ::  \<open>int_poly \<Rightarrow> (nat set \<times> int_poly multiset) \<Rightarrow> (status \<times> (nat set \<times> int_poly multiset)) nres\<close>
where
  \<open>PAC_checker_specification2 spec A \<equiv> SPEC(PAC_checker_specification_spec spec A)\<close>


definition PAC_checker_specification_step_spec
  ::  \<open>pac_state \<Rightarrow> int_poly \<Rightarrow> pac_state \<Rightarrow> (status \<times> pac_state) \<Rightarrow> bool\<close>
where
  \<open>PAC_checker_specification_step_spec = (\<lambda>(\<V>\<^sub>0, A\<^sub>0) spec (\<V>, A) (b, B).
       (is_success b \<longrightarrow>
         \<Union>(vars ` set_mset A\<^sub>0) \<subseteq> \<V>\<^sub>0 \<and>
          \<Union>(vars ` set_mset A) \<subseteq> \<V> \<and> PAC_Format\<^sup>*\<^sup>* (\<V>\<^sub>0, A\<^sub>0) (\<V>, A) \<and> PAC_Format\<^sup>*\<^sup>* (\<V>, A) B) \<and>
       (is_found b \<longrightarrow> 
          \<Union>(vars ` set_mset A\<^sub>0) \<subseteq> \<V>\<^sub>0 \<and>
          \<Union>(vars ` set_mset A) \<subseteq> \<V> \<and> PAC_Format\<^sup>*\<^sup>* (\<V>\<^sub>0, A\<^sub>0) (\<V>, A) \<and> PAC_Format\<^sup>*\<^sup>* (\<V>, A) B \<and>
         spec \<in> pac_ideal (set_mset A\<^sub>0)))\<close>

abbreviation PAC_checker_specification_step2
  ::  \<open>pac_state \<Rightarrow> int_poly \<Rightarrow> pac_state \<Rightarrow> (status \<times> pac_state) nres\<close>
where
  \<open>PAC_checker_specification_step2 A\<^sub>0 spec A \<equiv> SPEC(PAC_checker_specification_step_spec A\<^sub>0  spec A)\<close>


definition normalize_poly_spec :: \<open>_\<close> where
  \<open>normalize_poly_spec p = SPEC (\<lambda>r. p - r \<in> ideal polynom_bool \<and> vars r \<subseteq> vars p)\<close>

lemma normalize_poly_spec_alt_def:
  \<open>normalize_poly_spec p = SPEC (\<lambda>r. r - p \<in> ideal polynom_bool \<and> vars r \<subseteq> vars p)\<close>
  unfolding normalize_poly_spec_def
  by (auto dest: ideal.span_neg)

definition mult_poly_spec :: \<open>int mpoly \<Rightarrow> int mpoly \<Rightarrow> int mpoly nres\<close> where
  \<open>mult_poly_spec p q = SPEC (\<lambda>r. p * q - r \<in> ideal polynom_bool)\<close>

definition check_add :: \<open>(nat, int mpoly) fmap \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int mpoly \<Rightarrow> bool nres\<close> where
  \<open>check_add A \<V> p q i r =
     SPEC(\<lambda>b. b \<longrightarrow> p \<in># dom_m A \<and> q \<in># dom_m A \<and> i \<notin># dom_m A \<and> vars r \<subseteq> \<V> \<and>
            the (fmlookup A p) + the (fmlookup A q) - r \<in>  ideal polynom_bool)\<close>

definition check_mult :: \<open>(nat, int mpoly) fmap \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> int mpoly \<Rightarrow> nat \<Rightarrow> int mpoly \<Rightarrow> bool nres\<close> where
  \<open>check_mult A \<V> p q i r =
     SPEC(\<lambda>b. b \<longrightarrow> p \<in># dom_m A \<and>i \<notin># dom_m A \<and> vars q \<subseteq> \<V> \<and> vars r \<subseteq> \<V> \<and>
            the (fmlookup A p) * q - r \<in>  ideal polynom_bool)\<close>

definition check_extension :: \<open>(nat, int mpoly) fmap \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> int mpoly \<Rightarrow> (bool \<times> nat) nres\<close> where
  \<open>check_extension A \<V> i p =
     SPEC(\<lambda>(b, v). b \<longrightarrow> (i \<notin># dom_m A \<and>
     (v \<notin> \<V> \<and>
        ((coeff p (Poly_Mapping.single v 1) = 1 \<and>
           (Var v - p)\<^sup>2 - (Var v - p) \<in> ideal polynom_bool \<and>
            vars (Var v - p) \<subseteq> \<V> \<and>
            v \<notin> vars (Var v - p)) \<or>
        (coeff p (Poly_Mapping.single v 1) = -1 \<and>
           (Var v + p)\<^sup>2 - (Var v + p) \<in> ideal polynom_bool \<and>
            vars (Var v + p) \<subseteq> \<V> \<and>
            v \<notin> vars (Var v + p))))))\<close>

fun merge_status where
  \<open>merge_status (FAILED) _ = FAILED\<close> |
  \<open>merge_status _ (FAILED) = FAILED\<close> |
  \<open>merge_status FOUND _ = FOUND\<close> |
  \<open>merge_status _ FOUND = FOUND\<close> |
  \<open>merge_status _ _ = SUCCESS\<close>

type_synonym fpac_step = \<open>nat set \<times> (nat, int_poly) fmap\<close>

definition check_del :: \<open>(nat, int mpoly) fmap \<Rightarrow> nat \<Rightarrow> bool nres\<close> where
  \<open>check_del A p =
     SPEC(\<lambda>b. b \<longrightarrow> p \<in># dom_m A)\<close>

definition PAC_checker_step
  ::  \<open>int_poly \<Rightarrow> (status \<times> fpac_step) \<Rightarrow> int_poly pac_step \<Rightarrow>
    (status \<times> fpac_step) nres\<close>
where
  \<open>PAC_checker_step = (\<lambda>spec (stat, (\<V>, A)) st. case st of
     Add _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly_spec (pac_res st);
        eq \<leftarrow> check_add A \<V> (pac_src1 st) (pac_src2 st) (new_id st) r;
        st' \<leftarrow> SPEC(\<lambda>st'. (\<not>is_failed st' \<and> is_found st' \<longrightarrow> r - spec \<in> ideal polynom_bool));
        if eq
        then RETURN (merge_status stat st',
          \<V>, fmupd (new_id st) r A)
        else RETURN (FAILED, (\<V>, A))
   }
   | Del _ \<Rightarrow>
       do {
        eq \<leftarrow> check_del A (pac_src1 st);
        if eq
        then RETURN (stat, (\<V>, fmdrop (pac_src1 st) A))
        else RETURN (FAILED, (\<V>, A))
   }
   | Mult _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly_spec (pac_res st);
         q \<leftarrow> normalize_poly_spec (pac_mult st);
        eq \<leftarrow> check_mult A \<V> (pac_src1 st) q (new_id st) r;
        st' \<leftarrow> SPEC(\<lambda>st'. (\<not>is_failed st' \<and> is_found st' \<longrightarrow> r - spec \<in> ideal polynom_bool));
        if eq
        then RETURN (merge_status stat st',
          \<V>, fmupd (new_id st) r A)
        else RETURN (FAILED, (\<V>, A))
   }
   | Extension _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly_spec (pac_res st);
        (eq, v) \<leftarrow> check_extension A \<V> (new_id st) r;
        if eq
        then RETURN (stat,
          insert v \<V>, fmupd (new_id st) r A)
        else RETURN (FAILED, (\<V>, A))
   }
 )\<close>

definition polys_rel :: \<open>((nat, int mpoly)fmap \<times> _) set\<close> where
\<open>polys_rel = {(A, B). B = (ran_m A)}\<close>

definition polys_rel_full :: \<open>((nat set \<times> (nat, int mpoly)fmap) \<times> _) set\<close> where
  \<open>polys_rel_full = {((\<V>, A), (\<V>' , B)). (A, B) \<in> polys_rel \<and> \<V> = \<V>'}\<close>

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
  \<open>x13 \<in>#dom_m A \<Longrightarrow> (A,B) \<in> polys_rel \<Longrightarrow>
   (fmdrop x13 A, remove1_mset (the (fmlookup A x13)) B) \<in> polys_rel\<close>
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

lemma [simp]: \<open>vars (Var x :: 'a :: {zero_neq_one} mpoly) = {x}\<close>
  by (auto simp: vars_def Var.rep_eq  Var\<^sub>0_def)

lemma vars_minus_Var_subset:
  \<open>vars (p' - Var x :: 'a :: {ab_group_add,one,zero_neq_one} mpoly) \<subseteq>  \<V> \<Longrightarrow> vars p' \<subseteq> insert x \<V>\<close>
  using vars_add[of \<open>p' - Var x\<close> \<open>Var x\<close>]
  by auto

lemma vars_add_Var_subset:
  \<open>vars (p' + Var x :: 'a :: {ab_group_add,one,zero_neq_one} mpoly) \<subseteq>  \<V> \<Longrightarrow> vars p' \<subseteq> insert x \<V>\<close>
  using vars_add[of \<open>p' + Var x\<close> \<open>-Var x\<close>]
  by auto

lemma coeff_monomila_in_varsD:
  \<open>coeff p (monomial (Suc 0) x) \<noteq> 0 \<Longrightarrow> x \<in> vars (p :: int mpoly)\<close>
  by (auto simp: coeff_def vars_def keys_def
    intro!: exI[of _ \<open>monomial (Suc 0) x\<close>])

lemma PAC_Format_add_and_remove:
  \<open>r - x14 \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       (A, B) \<in> polys_rel \<Longrightarrow>
       x12 \<in># dom_m A \<Longrightarrow>
       x13 \<notin># dom_m A \<Longrightarrow>
       vars r \<subseteq> \<V> \<Longrightarrow>
       2 * the (fmlookup A x12) - r \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       PAC_Format\<^sup>*\<^sup>* (\<V>, B) (\<V>, remove1_mset (the (fmlookup A x12)) (add_mset r B))\<close>
   \<open>r - x14 \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       (A, B) \<in> polys_rel \<Longrightarrow>
       the (fmlookup A x11) + the (fmlookup A x12) - r \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       x11 \<in># dom_m A \<Longrightarrow>
       x12 \<in># dom_m A \<Longrightarrow>
       vars r \<subseteq> \<V> \<Longrightarrow>
       PAC_Format\<^sup>*\<^sup>* (\<V>, B) (\<V>, add_mset r B)\<close>
   \<open>r - x14 \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       (A, B) \<in> polys_rel \<Longrightarrow>
       x11 \<in># dom_m A \<Longrightarrow>
       x12 \<in># dom_m A \<Longrightarrow>
       the (fmlookup A x11) + the (fmlookup A x12) - r \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       vars r \<subseteq> \<V> \<Longrightarrow>
       x11 \<noteq> x12 \<Longrightarrow>
       PAC_Format\<^sup>*\<^sup>* (\<V>, B)
        (\<V>, add_mset r B - {#the (fmlookup A x11), the (fmlookup A x12)#})\<close>
   \<open>(A, B) \<in> polys_rel \<Longrightarrow>
       r - x34 \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       x11 \<in># dom_m A \<Longrightarrow>
       the (fmlookup A x11) * x32 - r \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       vars x32 \<subseteq> \<V> \<Longrightarrow>
       vars r \<subseteq> \<V> \<Longrightarrow>
       PAC_Format\<^sup>*\<^sup>* (\<V>, B) (\<V>, add_mset r B)\<close>
   \<open>(A, B) \<in> polys_rel \<Longrightarrow>
       r - x34 \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       x11 \<in># dom_m A \<Longrightarrow>
       the (fmlookup A x11) * x32 - r \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       vars x32 \<subseteq> \<V> \<Longrightarrow>
       vars r \<subseteq> \<V> \<Longrightarrow>
       PAC_Format\<^sup>*\<^sup>* (\<V>, B) (\<V>, remove1_mset (the (fmlookup A x11)) (add_mset r B))\<close>
  \<open>(A, B) \<in> polys_rel \<Longrightarrow>
       x12 \<in># dom_m A \<Longrightarrow>
       PAC_Format\<^sup>*\<^sup>* (\<V>, B) (\<V>, remove1_mset (the (fmlookup A x12)) B)\<close>
   \<open>(A, B) \<in> polys_rel \<Longrightarrow>
       coeff p' (Poly_Mapping.single x 1) = 1 \<Longrightarrow>
       (Var x - p')\<^sup>2 - (Var x - p') \<in> ideal polynom_bool \<Longrightarrow>
       x \<notin> \<V> \<Longrightarrow>
       x \<notin> vars(p' - Var x) \<Longrightarrow>
       vars(p' - Var x) \<subseteq> \<V> \<Longrightarrow>
       PAC_Format\<^sup>*\<^sup>* (\<V>, B)
         (insert x \<V>, add_mset p' B)\<close>
   \<open>(A, B) \<in> polys_rel \<Longrightarrow>
       coeff p' (Poly_Mapping.single x 1) = -1 \<Longrightarrow>
       (Var x + p')\<^sup>2 - (Var x + p') \<in> ideal polynom_bool \<Longrightarrow>
       x \<notin> \<V> \<Longrightarrow>
       x \<notin> vars(p' + Var x) \<Longrightarrow>
       vars(p' + Var x) \<subseteq> \<V> \<Longrightarrow>
       PAC_Format\<^sup>*\<^sup>* (\<V>, B)
         (insert x \<V>, add_mset p' B)\<close>
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
    apply (rule PAC_Format.mult[of \<open>the (fmlookup A x11)\<close> B \<open>x32\<close> r])
    apply (auto dest: polys_rel_in_dom_inD)
    done
  subgoal
    apply (rule rtranclp_trans)
    apply (rule H2; assumption)
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule PAC_Format.del[of \<open>the (fmlookup A x11)\<close>])
    apply (auto dest: polys_rel_in_dom_inD)
    done
  subgoal
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule PAC_Format.del[of \<open>the (fmlookup A x12)\<close> B])
    apply (auto dest: polys_rel_in_dom_inD)
    done
  subgoal
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule PAC_Format.extend_pos[of x p'])
    using coeff_monomila_in_varsD[of p' x]
    apply (auto dest: polys_rel_in_dom_inD)
    apply (subgoal_tac \<open>\<V> \<union> {x \<in> vars p'. x \<notin> \<V>} = insert x \<V>\<close>)
    apply simp
    using coeff_monomila_in_varsD[of p' x]
    apply (auto dest: vars_minus_Var_subset polys_rel_in_dom_inD)[]
    done
  subgoal
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule PAC_Format.extend_minus[of x p'])
    using coeff_monomila_in_varsD[of p' x]
    apply (auto dest: polys_rel_in_dom_inD vars_minus_Var_subset)
    apply (subgoal_tac \<open>\<V> \<union> {x \<in> vars p'. x \<notin> \<V>} = insert x \<V>\<close>)
    apply simp
    apply (auto dest: vars_add_Var_subset polys_rel_in_dom_inD)
    done
  done


abbreviation status_rel :: \<open>(status \<times> status) set\<close> where
  \<open>status_rel \<equiv> Id\<close>

lemma is_merge_status[simp]:
  \<open>is_failed (merge_status a st') \<longleftrightarrow> is_failed a \<or> is_failed st'\<close>
  \<open>is_found (merge_status a st') \<longleftrightarrow> \<not>is_failed a \<and> \<not>is_failed st' \<and> (is_found a \<or> is_found st')\<close>
  \<open>is_success (merge_status a st') \<longleftrightarrow> (is_success a \<and> is_success st')\<close>
  by (cases a; cases st'; auto; fail)+

lemma status_rel_merge_status:
  \<open>(merge_status a b, SUCCESS) \<notin> status_rel \<longleftrightarrow>
    (a = FAILED) \<or> (b = FAILED) \<or>
    a = FOUND \<or> (b = FOUND)\<close>
  by (cases a; cases b; auto)

lemma Ex_status_iff:
  \<open>(\<exists>a. P a) \<longleftrightarrow> P SUCCESS \<or> P FOUND \<or> (P (FAILED))\<close>
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
  \<open>merge_status SUCCESS a = FAILED \<longleftrightarrow> a = FAILED\<close>
  \<open>merge_status a SUCCESS = FAILED \<longleftrightarrow> a = FAILED\<close>
  \<open>merge_status FOUND a = FAILED \<longleftrightarrow> a = FAILED\<close>
  \<open>merge_status a FOUND = FAILED \<longleftrightarrow> a = FAILED\<close>
  \<open>merge_status a FOUND = SUCCESS \<longleftrightarrow> False\<close>
  \<open>merge_status a b = FOUND \<longleftrightarrow> (a = FOUND \<or> b = FOUND) \<and> (a \<noteq> FAILED \<and> b \<noteq> FAILED)\<close>
  apply (cases a; auto; fail)+
  apply (cases a; cases b; auto; fail)+
  done

lemma PAC_checker_step_PAC_checker_specification2:
  fixes a :: \<open>status\<close>
  assumes AB: \<open>((\<V>, A),(\<V>\<^sub>B, B)) \<in> polys_rel_full\<close> and
    \<open>\<not>is_failed a\<close> and
    [simp,intro]: \<open>a = FOUND \<Longrightarrow> spec \<in> pac_ideal (set_mset A\<^sub>0)\<close> and
    A\<^sub>0B: \<open>PAC_Format\<^sup>*\<^sup>* (\<V>\<^sub>0, A\<^sub>0) (\<V>, B)\<close> and
    spec\<^sub>0: \<open>vars spec \<subseteq> \<V>\<^sub>0\<close>  and
    vars_A\<^sub>0: \<open>\<Union> (vars ` set_mset A\<^sub>0) \<subseteq> \<V>\<^sub>0\<close>
  shows \<open>PAC_checker_step spec (a, (\<V>, A)) st \<le> \<Down> (status_rel \<times>\<^sub>r polys_rel_full) (PAC_checker_specification_step2 (\<V>\<^sub>0, A\<^sub>0) spec (\<V>, B))\<close>
proof -
  have
    \<open>\<V>\<^sub>B = \<V>\<close>and
    [simp, intro]:\<open>(A, B) \<in> polys_rel\<close>
    using AB
    by (auto simp: polys_rel_full_def)
  have H1: \<open> x12 \<in># dom_m A \<Longrightarrow>
       2 * the (fmlookup A x12) - r \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       r - spec \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       vars spec \<subseteq> vars r \<Longrightarrow>
       spec \<in> pac_ideal (set_mset B)\<close> for x12 r
     using \<open>(A,B) \<in> polys_rel\<close>
      ideal.span_add[OF ideal.span_add[OF ideal.span_neg ideal.span_neg,
         of \<open>the (fmlookup A x12)\<close> _  \<open>the (fmlookup A x12)\<close>],
      of \<open>set_mset B \<union> polynom_bool\<close> \<open>2 * the (fmlookup A x12) - r\<close>]
     unfolding polys_rel_def
     apply (subgoal_tac \<open>r \<in> pac_ideal (set_mset B)\<close>)
     apply (auto dest!: multi_member_split simp: ran_m_def intro: diff_in_polynom_bool_pac_idealI)
     by (metis (no_types, lifting) ab_semigroup_mult_class.mult.commute diff_in_polynom_bool_pac_idealI
       ideal.span_base pac_idealI3 set_image_mset set_mset_add_mset_insert union_single_eq_member)

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
     apply (auto dest!: multi_member_split simp: ran_m_def ideal.span_base intro: diff_in_polynom_bool_pac_idealI)
     by (metis (mono_tags, lifting) Un_insert_left diff_diff_eq2 diff_in_polynom_bool_pac_idealI diff_zero
       ideal.span_diff ideal.span_neg minus_diff_eq pac_idealI1 pac_ideal_def set_image_mset
       set_mset_add_mset_insert union_single_eq_member)

  have H3: \<open>x12 \<in># dom_m A \<Longrightarrow>
       the (fmlookup A x12) * q - r \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       r - spec \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       spec \<in> pac_ideal (set_mset B)\<close> for x12 r q
     using \<open>(A,B) \<in> polys_rel\<close>
      ideal.span_add[OF ideal.span_add[OF ideal.span_neg ideal.span_neg,
         of \<open>the (fmlookup A x12)\<close> _  \<open>the (fmlookup A x12)\<close>],
      of \<open>set_mset B \<union> polynom_bool\<close> \<open>2 * the (fmlookup A x12) - r\<close>]
     unfolding polys_rel_def
     apply (subgoal_tac \<open>r \<in> pac_ideal (set_mset B)\<close>)
     apply (auto dest!: multi_member_split simp: ran_m_def intro: diff_in_polynom_bool_pac_idealI)
     by (metis (no_types, lifting) ab_semigroup_mult_class.mult.commute diff_in_polynom_bool_pac_idealI
       ideal.span_base pac_idealI3 set_image_mset set_mset_add_mset_insert union_single_eq_member)

  have [intro]: \<open>spec \<in> pac_ideal (set_mset B) \<Longrightarrow> spec \<in> pac_ideal (set_mset A\<^sub>0)\<close> and
    vars_B: \<open>\<Union> (vars ` set_mset B) \<subseteq> \<V>\<close>and
    vars_B: \<open>\<Union> (vars ` set_mset (ran_m A)) \<subseteq> \<V>\<close>
    using rtranclp_PAC_Format_subset_ideal[OF A\<^sub>0B  vars_A\<^sub>0] spec\<^sub>0 \<open>(A, B) \<in> polys_rel\<close>[unfolded polys_rel_def, simplified]
    by (smt in_mono mem_Collect_eq restricted_ideal_to_def)+

  have eq_successI: \<open>st' \<noteq> FAILED \<Longrightarrow>
       st' \<noteq> FOUND \<Longrightarrow> st' = SUCCESS\<close> for st'
    by (cases st') auto
  have vars_diff_inv: \<open>vars (Var x2 - r) = vars (r - Var x2 :: int mpoly)\<close> for x2 r
    using vars_uminus[of \<open>Var x2 - r\<close>]
    by (auto simp del: vars_uminus)
  have vars_add_inv: \<open>vars (Var x2 + r) = vars (r + Var x2 :: int mpoly)\<close> for x2 r
    unfolding add.commute[of \<open>Var x2\<close> r] ..

  have [iff]: \<open>a \<noteq> FAILED\<close> and
    [intro]: \<open>a \<noteq> SUCCESS \<Longrightarrow> a = FOUND\<close> and
    [simp]: \<open>merge_status a FOUND = FOUND\<close>
    using assms(2) by (cases a; auto)+
  note [[goals_limit=1]]
  show ?thesis
    unfolding PAC_checker_step_def PAC_checker_specification_step_spec_def
      normalize_poly_spec_alt_def check_mult_def check_add_def
      check_extension_def polys_rel_full_def
    apply (cases st)
    apply clarsimp_all
    subgoal for x11 x12 x13 x14
      apply (refine_vcg lhs_step_If)
      subgoal for r eqa st'
        using assms vars_B apply -
        apply (rule RETURN_SPEC_refine)
        apply (rule_tac x = \<open>(merge_status a st',\<V>,add_mset r B)\<close> in exI)
        by (auto simp: polys_rel_update_remove ran_m_mapsto_upd_notin
          intro: PAC_Format_add_and_remove H2 dest: rtranclp_PAC_Format_subset_ideal)
      subgoal
        by (rule RETURN_SPEC_refine)
         (auto simp: Ex_status_iff dest: rtranclp_PAC_Format_subset_ideal)
      done
    subgoal for x11 x12 x13 x14
      apply (refine_vcg lhs_step_If)
      subgoal for r q eqa st'
        using assms vars_B apply -
        apply (rule RETURN_SPEC_refine)
        apply (rule_tac x = \<open>(merge_status a st',\<V>,add_mset r B)\<close> in exI)
        by (auto intro: polys_rel_update_remove intro: PAC_Format_add_and_remove(3-) H3
           dest: rtranclp_PAC_Format_subset_ideal)
      subgoal
        by (rule RETURN_SPEC_refine)
          (auto simp: Ex_status_iff)
      done
    subgoal for x31 x32
      apply (refine_vcg lhs_step_If)
      subgoal for r x x1 x2
        using assms vars_B apply -
        apply (rule RETURN_SPEC_refine)
        apply (rule_tac x = \<open>(a,insert x2 \<V>, add_mset r B)\<close> in exI)
        apply (auto simp: intro: polys_rel_update_remove PAC_Format_add_and_remove(5-)
           dest: rtranclp_PAC_Format_subset_ideal)
        apply (rule PAC_Format_add_and_remove(5-))
        apply (auto simp: vars_diff_inv)
        apply (rule PAC_Format_add_and_remove(5-))
        apply (auto simp: vars_diff_inv)
        apply (rule PAC_Format_add_and_remove(8-))
        apply (auto simp: vars_add_inv)
        apply (rule PAC_Format_add_and_remove(8-))
        apply (auto simp: vars_add_inv)
        done
      subgoal
        by (rule RETURN_SPEC_refine)
          (auto simp: Ex_status_iff)
      done
    subgoal for x11
      unfolding check_del_def
      apply (refine_vcg lhs_step_If)
      subgoal for eq
        using assms vars_B apply -
        apply (rule RETURN_SPEC_refine)
        apply (rule_tac x = \<open>(a,\<V>, remove1_mset (the (fmlookup A x11)) B)\<close> in exI)
        apply (auto simp: polys_rel_update_remove PAC_Format_add_and_remove
             is_failed_def is_success_def is_found_def
          dest!: eq_successI
          split: if_splits
          dest: rtranclp_PAC_Format_subset_ideal
          intro: PAC_Format_add_and_remove H3)
        done
      subgoal
        by (rule RETURN_SPEC_refine)
          (auto simp: Ex_status_iff)
      done
    done
qed


definition PAC_checker
  :: \<open>int_poly \<Rightarrow> fpac_step \<Rightarrow> status \<Rightarrow> int_poly pac_step list \<Rightarrow>
    (status \<times> fpac_step) nres\<close>
where
  \<open>PAC_checker spec A b st = do {
    (S, _) \<leftarrow> WHILE\<^sub>T
       (\<lambda>((b :: status, A :: fpac_step), st). \<not>is_failed b \<and> st \<noteq> [])
       (\<lambda>((bA), st). do {
          ASSERT(st \<noteq> []);
          S \<leftarrow> PAC_checker_step spec (bA) (hd st);
          RETURN (S, tl st)
        })
      ((b, A), st);
    RETURN S
  }\<close>


lemma PAC_checker_specification_spec_trans:
  \<open>PAC_checker_specification_spec spec A (st, x2) \<Longrightarrow>
    PAC_checker_specification_step_spec A spec x2 (st', x1a) \<Longrightarrow>
    PAC_checker_specification_spec spec A (st', x1a)\<close>
 unfolding PAC_checker_specification_spec_def
   PAC_checker_specification_step_spec_def
 by auto

lemma RES_SPEC_eq:
  \<open>RES \<Phi> = SPEC(\<lambda>P. P \<in> \<Phi>)\<close>
  by auto

lemma is_failed_is_success_completeD:
  \<open>\<not> is_failed x \<Longrightarrow> \<not>is_success x \<Longrightarrow> is_found x\<close>
  by (cases x) auto

lemma PAC_checker_PAC_checker_specification2:
  \<open>(A, B) \<in>  polys_rel_full \<Longrightarrow>
    \<not>is_failed a \<Longrightarrow>
    (a = FOUND \<Longrightarrow> spec \<in> pac_ideal (set_mset (snd B))) \<Longrightarrow>
    \<Union>(vars ` set_mset (ran_m (snd A))) \<subseteq> fst B \<Longrightarrow>
    vars spec \<subseteq> fst B \<Longrightarrow>
  PAC_checker spec A a st \<le> \<Down> (status_rel \<times>\<^sub>r polys_rel_full) (PAC_checker_specification2 spec B)\<close>
  unfolding PAC_checker_def conc_fun_RES
  apply (subst RES_SPEC_eq)
  apply (refine_vcg WHILET_rule[where
      I = \<open>\<lambda>((bB), st). bB \<in> (status_rel \<times>\<^sub>r polys_rel_full)\<inverse> ``
                      Collect (PAC_checker_specification_spec spec B)\<close>
    and R = \<open>measure (\<lambda>(_, st).  Suc (length st))\<close>])
  subgoal by auto
  subgoal apply (auto simp: PAC_checker_specification_spec_def)
    apply (cases B; cases A)
    apply (auto simp:polys_rel_def polys_rel_full_def Image_iff)
    done
  subgoal by auto
  subgoal
    apply auto
    apply (rule
     PAC_checker_step_PAC_checker_specification2[of _ _ _ _ _ _ _ \<open>fst B\<close>, THEN order_trans])
     apply assumption
     apply assumption
     apply (auto intro: PAC_checker_specification_spec_trans simp: conc_fun_RES)
     apply (auto simp: PAC_checker_specification_spec_def polys_rel_full_def polys_rel_def
       dest: PAC_Format_subset_ideal
       dest: is_failed_is_success_completeD; fail)+
     apply (auto simp: Image_iff intro: PAC_checker_specification_spec_trans)
     by (metis (mono_tags, lifting) PAC_checker_specification_spec_trans mem_Collect_eq old.prod.case
       polys_rel_def polys_rel_full_def prod.collapse)
  subgoal
    by auto
  done

definition remap_polys_polynom_bool :: \<open>int mpoly \<Rightarrow> nat set \<Rightarrow> (nat, int_poly) fmap \<Rightarrow> (status \<times> fpac_step) nres\<close> where
\<open>remap_polys_polynom_bool spec = (\<lambda>\<V> A.
   SPEC(\<lambda>(st, \<V>', A'). dom_m A = dom_m A' \<and>
      (\<forall>i \<in># dom_m A. the (fmlookup A i) - the (fmlookup A' i) \<in> ideal polynom_bool) \<and>
      \<Union>(vars ` set_mset (ran_m A)) \<subseteq> \<V>' \<and>
      \<Union>(vars ` set_mset (ran_m A')) \<subseteq> \<V>' \<and>
    (st = FOUND \<longrightarrow> spec \<in># ran_m A') \<and>
    \<not>is_failed st))\<close>

definition remap_polys_change_all :: \<open>int mpoly \<Rightarrow> nat set \<Rightarrow> (nat, int_poly) fmap \<Rightarrow> (status \<times> fpac_step) nres\<close> where
\<open>remap_polys_change_all spec = (\<lambda>\<V> A. SPEC (\<lambda>(st, \<V>', A').
    pac_ideal (set_mset (ran_m A)) = pac_ideal (set_mset (ran_m A')) \<and>
    (st = FOUND \<longrightarrow> spec \<in># ran_m A') \<and>
    \<Union>(vars ` set_mset (ran_m A)) \<subseteq> \<V>' \<and>
    \<Union>(vars ` set_mset (ran_m A')) \<subseteq> \<V>' \<and>
    \<not>is_failed st))\<close>

lemma fmap_eq_dom_iff:
  \<open>A = A' \<longleftrightarrow> dom_m A = dom_m A' \<and> (\<forall>i \<in># dom_m A. the (fmlookup A i) = the (fmlookup A' i))\<close>
  apply auto
  by (metis fmap_ext in_dom_m_lookup_iff option.collapse)

lemma ideal_remap_incl:
  \<open>finite A' \<Longrightarrow> (\<forall>a'\<in>A'. \<exists>a\<in>A. a-a' \<in> B) \<Longrightarrow> ideal (A' \<union> B) \<subseteq> ideal (A \<union> B)\<close>
  apply (induction A' rule: finite_induct)
  apply (auto intro: ideal.span_mono)
  using ideal.span_mono sup_ge2 apply blast
  proof -
    fix x :: 'a and F :: "'a set" and xa :: 'a and a :: 'a
    assume a1: "a \<in> A"
    assume a2: "a - x \<in> B"
    assume a3: "xa \<in> More_Modules.ideal (insert x (F \<union> B))"
    assume a4: "More_Modules.ideal (F \<union> B) \<subseteq> More_Modules.ideal (A \<union> B)"
    have "x \<in> More_Modules.ideal (A \<union> B)"
      using a2 a1 by (metis (no_types, lifting) Un_upper1 Un_upper2 add_diff_cancel_left' diff_add_cancel
        ideal.module_axioms ideal.span_diff in_mono module.span_superset)
    then show "xa \<in> More_Modules.ideal (A \<union> B)"
      using a4 a3 ideal.span_insert_subset by blast
  qed

lemma pac_ideal_remap_eq:
  \<open>dom_m b = dom_m ba \<Longrightarrow>
       \<forall>i\<in>#dom_m ba.
          the (fmlookup b i) - the (fmlookup ba i)
          \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
     pac_ideal ((\<lambda>x. the (fmlookup b x)) ` set_mset (dom_m ba)) = pac_ideal ((\<lambda>x. the (fmlookup ba x)) ` set_mset (dom_m ba))\<close>
  unfolding pac_ideal_alt_def
  apply standard
  subgoal
    apply (rule ideal_remap_incl)
    apply (auto dest!: multi_member_split
      dest: ideal.span_neg)
    apply (drule ideal.span_neg)
    apply auto
    done
  subgoal
    by (rule ideal_remap_incl)
     (auto dest!: multi_member_split)
  done

lemma remap_polys_polynom_bool_remap_polys_change_all:
  \<open>remap_polys_polynom_bool spec \<V> A \<le> remap_polys_change_all spec \<V> A\<close>
  unfolding remap_polys_polynom_bool_def remap_polys_change_all_def
  apply (simp add: ideal.span_zero fmap_eq_dom_iff ideal.span_eq)
  apply (auto dest: multi_member_split simp: ran_m_def ideal.span_base pac_ideal_remap_eq
    add_mset_eq_add_mset
    eq_commute[of \<open>add_mset _ _\<close> \<open>dom_m (A :: (nat, int mpoly)fmap)\<close> for A])
  done


definition remap_polys :: \<open>int mpoly \<Rightarrow> nat set \<Rightarrow> (nat, int_poly) fmap \<Rightarrow> (status \<times> fpac_step) nres\<close> where
  \<open>remap_polys spec = (\<lambda>\<V> A. do{
   dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
   (b, N) \<leftarrow> FOREACH dom
     (\<lambda>i (b, \<V>, A').
        if i \<in># dom_m A
        then do {
          p \<leftarrow> SPEC(\<lambda>p. the (fmlookup A i) - p \<in> ideal polynom_bool \<and> vars p \<subseteq> vars (the (fmlookup A i)));
          eq \<leftarrow> SPEC(\<lambda>eq. eq \<longrightarrow> p = spec);
          \<V> \<leftarrow> SPEC(\<lambda>\<V>'. \<V> \<union> vars (the (fmlookup A i)) \<subseteq> \<V>');
          RETURN(b \<or> eq, \<V>, fmupd i p A')
        } else RETURN (b, \<V>, A'))
     (False, \<V>, fmempty);
     RETURN (if b then FOUND else SUCCESS, N)
 })\<close>

lemma remap_polys_spec:
  \<open>remap_polys spec \<V> A \<le> remap_polys_polynom_bool spec \<V> A\<close>
  unfolding remap_polys_def remap_polys_polynom_bool_def
  apply (refine_vcg FOREACH_rule[where
    I = \<open>\<lambda>dom (b, \<V>, A').
      set_mset (dom_m A') =  set_mset (dom_m A) - dom \<and>
      (\<forall>i \<in> set_mset (dom_m A) - dom. the (fmlookup A i) - the (fmlookup A' i) \<in> ideal polynom_bool) \<and>
     \<Union>(vars ` set_mset (ran_m (fmrestrict_set (set_mset (dom_m A')) A))) \<subseteq> \<V> \<and>
     \<Union>(vars ` set_mset (ran_m A')) \<subseteq> \<V> \<and>
      (b \<longrightarrow> spec \<in># ran_m A')\<close>])
  subgoal by auto
  subgoal by auto
  subgoal
    by auto
  subgoal by auto
  subgoal using ideal.span_add by auto
  subgoal by auto
  subgoal
    apply clarsimp
    apply (auto simp: )
    done
  subgoal
    apply clarsimp
    apply (auto simp: )
    done
   subgoal
     supply[[goals_limit=1]]
     by (auto simp add: ran_m_mapsto_upd_notin dom_m_fmrestrict_set' subset_eq)
   subgoal
     supply[[goals_limit=1]]
     by (auto simp add: ran_m_mapsto_upd_notin dom_m_fmrestrict_set' subset_eq)
   subgoal
     by (auto simp: ran_m_mapsto_upd_notin)
   subgoal
     by auto
   subgoal
     by auto
   subgoal
     by (auto simp add: ran_m_mapsto_upd_notin dom_m_fmrestrict_set' subset_eq)
   subgoal
     by (auto simp add: ran_m_mapsto_upd_notin dom_m_fmrestrict_set' subset_eq)
   subgoal
     by auto
   subgoal
     by (auto simp: distinct_set_mset_eq_iff[symmetric] distinct_mset_dom)
   subgoal
     by (auto simp: distinct_set_mset_eq_iff[symmetric] distinct_mset_dom)
   subgoal
     by (auto simp add: ran_m_mapsto_upd_notin dom_m_fmrestrict_set' subset_eq
       fmlookup_restrict_set_id')
   subgoal
     by (auto simp add: ran_m_mapsto_upd_notin dom_m_fmrestrict_set' subset_eq)
   subgoal
     by (auto simp add: ran_m_mapsto_upd_notin dom_m_fmrestrict_set' subset_eq
       fmlookup_restrict_set_id')
   subgoal
     by (auto split: if_splits)
   done


definition full_checker
  :: \<open>int_poly \<Rightarrow> (nat, int_poly) fmap \<Rightarrow> int_poly pac_step list \<Rightarrow> (status \<times> _) nres\<close>
 where
  \<open>full_checker spec0 A pac = do {
     spec \<leftarrow> normalize_poly_spec spec0;
     (st, \<V>, A) \<leftarrow> remap_polys_change_all spec {} A;
     \<V> \<leftarrow> SPEC(\<lambda>\<V>'. \<V> \<union> vars spec0 \<subseteq> \<V>');
     PAC_checker spec (\<V>, A) st pac
}\<close>

lemma restricted_ideal_to_mono:
  \<open>restricted_ideal_to\<^sub>I \<V> I \<subseteq> restricted_ideal_to\<^sub>I \<V>' J \<Longrightarrow>
  \<U> \<subseteq> \<V> \<Longrightarrow>
   restricted_ideal_to\<^sub>I \<U> I \<subseteq> restricted_ideal_to\<^sub>I \<U>  J\<close>
  by (auto simp: restricted_ideal_to_def)


lemma full_checker_spec:
  assumes \<open>(A, A') \<in> polys_rel\<close>
  shows
    \<open>full_checker spec A pac \<le> \<Down> (status_rel \<times>\<^sub>r polys_rel_full) (PAC_checker_specification (A') spec)\<close>
proof -
  have H: \<open>set_mset b \<subseteq> pac_ideal (set_mset (ran_m A)) \<Longrightarrow>
       x \<in> pac_ideal (set_mset b) \<Longrightarrow> x \<in> pac_ideal (set_mset A')\<close> for b x
   using assms apply (auto simp: polys_rel_def)
   by (metis (no_types, lifting) ideal.span_subset_spanI ideal.span_superset le_sup_iff pac_ideal_alt_def subsetD)
  have 1: \<open>x \<in> {(st, \<V>', A').
            pac_ideal (set_mset (ran_m x2)) =
            pac_ideal (set_mset (ran_m A')) \<and>
            (st = FOUND \<longrightarrow> speca \<in># ran_m A') \<and>
            \<Union> (vars ` set_mset (ran_m ABC)) \<subseteq> \<V>' \<and>
            \<Union> (vars ` set_mset (ran_m A')) \<subseteq> \<V>' \<and> \<not> is_failed st} \<Longrightarrow>
         x = (st, x') \<Longrightarrow> x' = (\<V>, Aa) \<Longrightarrow>((\<V>', Aa), \<V>', ran_m Aa) \<in> polys_rel_full\<close> for Aa speca x2 st x \<V>' \<V> x' ABC
       by (auto simp: polys_rel_def polys_rel_full_def)
  show ?thesis
    supply[[goals_limit=1]]
    unfolding full_checker_def normalize_poly_spec_def
      PAC_checker_specification_def remap_polys_change_all_def
    apply (refine_vcg PAC_checker_PAC_checker_specification2[THEN order_trans, of _ _])
    apply (rule 1; assumption)
    subgoal
      using fmap_ext assms by (auto simp: polys_rel_def ran_m_def)
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal for speca x1 x2 x x1a x2a x1b
      apply (rule ref_two_step[OF order.refl])
      using assms
      apply (auto simp add: PAC_checker_specification_spec_def conc_fun_RES polys_rel_def polys_rel_full_def
        dest!: rtranclp_PAC_Format_subset_ideal dest: is_failed_is_success_completeD)
      apply (drule restricted_ideal_to_mono[of _ _ _ _ \<open>\<Union> (vars ` set_mset (ran_m A)) \<union> vars spec\<close>])
      apply auto[]
      apply auto[]
      apply (metis (no_types, lifting) group_eq_aux ideal.span_add ideal.span_base in_mono pac_ideal_alt_def sup.cobounded2)
      apply (smt le_sup_iff restricted_ideal_to_mono subsetD subset_trans sup_ge1 sup_ge2)
      apply (smt le_sup_iff restricted_ideal_to_mono subsetD subset_trans sup_ge1 sup_ge2)
      apply (metis (no_types, lifting) cancel_comm_monoid_add_class.diff_cancel diff_add_eq
        diff_in_polynom_bool_pac_idealI group_eq_aux ideal.span_add_eq2)
      apply (drule restricted_ideal_to_mono[of _ _ _ _ \<open>\<Union> (vars ` set_mset (ran_m A)) \<union> vars spec\<close>])
      apply auto[]
      apply auto[]
      apply (metis (no_types, lifting) group_eq_aux ideal.span_add ideal.span_base in_mono pac_ideal_alt_def sup.cobounded2)
      apply (smt le_sup_iff restricted_ideal_to_mono subsetD subset_trans sup_ge1 sup_ge2)
      apply (drule restricted_ideal_to_mono[of _ _ _ _ \<open>\<Union> (vars ` set_mset (ran_m A)) \<union> vars spec\<close>])
      apply auto[]
      apply auto[]
      apply (metis (no_types, lifting) group_eq_aux ideal.span_add ideal.span_base in_mono pac_ideal_alt_def sup.cobounded2)
      done
   done
qed


end

