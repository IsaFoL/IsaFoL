theory PAC_Checker_Specification
  imports PAC_Specification
     Refine_Imperative_HOL.IICF
     Weidenbach_Book_Base.WB_List_More

begin

datatype pac_step =
  AddD (pac_src1: int_poly) (pac_src2: int_poly) (pac_res: int_poly) |
  Add (pac_src1: int_poly) (pac_src2: int_poly) (pac_res: int_poly) |
  MultD (pac_src1: int_poly) (pac_src2: int_poly) (pac_res: int_poly) |
  Mult (pac_src1: int_poly) (pac_src2: int_poly) (pac_res: int_poly)


definition PAC_checker_specification ::  \<open>int_poly multiset \<Rightarrow> (bool \<times> int_poly multiset) nres\<close> where
  \<open>PAC_checker_specification A = SPEC(\<lambda>(b, B). b \<longrightarrow> ideal (set_mset B) \<subseteq> ideal (set_mset A))\<close>

definition PAC_checker_specification_spec ::  \<open>int_poly multiset \<Rightarrow> (bool \<times> int_poly multiset) \<Rightarrow> bool\<close> where
  \<open>PAC_checker_specification_spec A = (\<lambda>(b, B). b \<longrightarrow> PAC_Format\<^sup>*\<^sup>* (set_mset A) (set_mset B))\<close>

abbreviation PAC_checker_specification2 ::  \<open>int_poly multiset \<Rightarrow> (bool \<times> int_poly multiset) nres\<close> where
  \<open>PAC_checker_specification2 A \<equiv> SPEC(PAC_checker_specification_spec A)\<close>

definition PAC_checker_step ::  \<open>int_poly multiset \<Rightarrow> pac_step \<Rightarrow> (bool \<times> int_poly multiset) nres\<close> where
  \<open>PAC_checker_step A st = (case st of
     AddD _ _ _ \<Rightarrow>
       do {
         eq \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> pac_src1 st \<in># A \<and> pac_src2 st \<in># A \<and>
            pac_src1 st + pac_src2 st - pac_res st \<in>  ideal polynom_bool);
        if eq
        then RETURN (True,
           removeAll_mset (pac_src1 st) (removeAll_mset (pac_src2 st) (add_mset (pac_res st) A)))
        else RETURN (False, A)
   }
  | Add _ _ _ \<Rightarrow>
       do {
         eq \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> pac_src1 st \<in># A \<and> pac_src2 st \<in># A \<and>
            pac_src1 st + pac_src2 st - pac_res st \<in>  ideal polynom_bool);
        if eq
        then RETURN (True, add_mset (pac_res st) A)
        else RETURN (False, A)
   }
  | MultD _ _ _ \<Rightarrow>
       do {
         eq \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> pac_src1 st \<in># A \<and>
            pac_src1 st * pac_src2 st - pac_res st \<in> ideal polynom_bool);
        if eq
        then RETURN (True,
           removeAll_mset (pac_src1 st) (removeAll_mset (pac_src2 st) (add_mset (pac_res st) A)))
        else RETURN (False, A)
   }
  | Mult _ _ _ \<Rightarrow>
       do {
         eq \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> pac_src1 st \<in># A \<and>
            pac_src1 st * pac_src2 st - pac_res st \<in>  ideal polynom_bool);
        if eq
        then RETURN (True, add_mset (pac_res st) A)
        else RETURN (False, A)
   }
 )\<close>

lemma PAC_checker_step_PAC_checker_specification2:
  \<open>PAC_checker_step A st \<le> PAC_checker_specification2 A\<close>
proof -
  have [simp]: \<open>set_mset
          (A -
           (replicate_mset (count A x12) x12 +
            replicate_mset (count A x11) x11)) =
        set_mset A - {x11} - {x12}\<close> for x11 x12
    by (auto dest: in_diffD simp: in_diff_count split: if_splits)
  have H[intro]: \<open>x11 \<in># A \<Longrightarrow> x12 \<in># A \<Longrightarrow> PAC_Format\<^sup>*\<^sup>* (set_mset A) (set_mset A - {x11} - {x12})\<close>
       for x11 x12
    by (metis Diff_empty Diff_insert0 del rtranclp.simps)
  have [intro]: \<open> x12 \<in># A \<Longrightarrow>
       2 * x12 - x13 \<in> More_Modules.ideal polynom_bool \<Longrightarrow>
       PAC_Format (set_mset A) (insert x13 (set_mset A))\<close> for x12 x13
     by (simp add: ab_semigroup_mult_class.mult.commute mult)
  show ?thesis
    unfolding PAC_checker_step_def PAC_checker_specification_spec_def
    apply (cases st)
    apply clarsimp_all
    subgoal
      apply refine_vcg
      apply (auto 6 4 simp: RETURN_def
        intro: PAC_Format.intros simp flip: insert_minus_eq)
      apply (auto intro: PAC_Format.intros)
      apply (metis Diff_empty Diff_insert0 add del mult_2 rtranclp.simps)
      by (metis (no_types, lifting) add del insertE insertI2 insert_Diff rtranclp.simps)
    subgoal
      by refine_vcg
        (auto 6 4 simp: RETURN_def
        intro: PAC_Format.intros simp flip: insert_minus_eq)
    subgoal
      apply refine_vcg
      apply (auto 6 4 simp: RETURN_def
        intro: PAC_Format.intros simp flip: insert_minus_eq)
      apply (auto intro: PAC_Format.intros)
      apply (metis Diff_empty Diff_insert0 del rtranclp.simps)
      apply (metis (no_types, lifting) del mult insertI2 rtranclp.simps)
      apply (metis Diff_insert Diff_insert0 H del r_into_rtranclp)
      by (metis (no_types, lifting) Diff_empty Diff_insert0 del mult rtranclp.simps)
    subgoal
      by refine_vcg
        (auto 6 4 simp: RETURN_def
        intro: PAC_Format.intros simp flip: insert_minus_eq)
    done
qed

definition PAC_checker:: \<open>int_poly multiset \<Rightarrow> pac_step list \<Rightarrow> (bool \<times> int_poly multiset) nres\<close> where
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

lemma PAC_checker_PAC_checker_specification2:
  \<open>PAC_checker A st \<le> (PAC_checker_specification2 A)\<close>
proof -
  show ?thesis
    unfolding PAC_checker_def
    apply (refine_vcg WHILET_rule[where \<Phi> = \<open>\<lambda>(B, _). PAC_checker_specification_spec A B\<close> and
        I = \<open>\<lambda>((bB), n). n \<le> length st \<and> (PAC_checker_specification_spec A bB)\<close>
      and R = \<open>measure (\<lambda>(_, n).  Suc (length st) - n)\<close>]
      PAC_checker_step_PAC_checker_specification2[THEN order_trans])
   subgoal by auto
   subgoal by auto
   subgoal by (auto simp: PAC_checker_specification_spec_def)
   subgoal by auto
   subgoal by auto
   subgoal by (auto intro: PAC_checker_specification_spec_trans)
   subgoal by auto
   subgoal by auto
   subgoal by auto
   done
qed

end