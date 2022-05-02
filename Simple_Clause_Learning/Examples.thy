theory Examples
  imports Simple_Clause_Learning
begin

locale example = scl renaming_vars inv_renaming_vars
  for renaming_vars inv_renaming_vars :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v" +
  fixes a b c d e f g :: "('f, 'v) term"
  assumes distinct_terms: "distinct [a, b, c, d, e, f, g]" and
    ball_is_ground_atm: "\<forall>t \<in> {a, b, c, d, e, f, g}. is_ground_atm t"
begin

definition C1 where
  "C1 = {#Neg a, Pos b#}"

definition C2 where
  "C2 = {#Neg a, Pos c#}"

definition C3 where
  "C3 = {#Neg b, Pos d#}"

definition C4 where
  "C4 = {#Neg c, Neg d#}"

definition C5 where
  "C5 = {#Pos e, Pos f, Pos g#}"

definition N where
  "N = {C1, C2, C3, C4, C5}"


lemma ball_is_ground_cls: "\<forall>C \<in> N. is_ground_cls C"
  using ball_is_ground_atm
  by (simp add: N_def C1_def C2_def C3_def C4_def C5_def is_ground_cls_def is_ground_lit_def)


definition S1 where
  "S1 = ([(Pos a, None)], {}, None)"

lemma "regular_scl N initial_state S1"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N initial_state S1"
    unfolding S1_def
    by (simp add: conflict.simps)
next
  have "decide N initial_state (trail_decide [] (Pos a), {}, None)"
    by (rule decideI)
      (simp_all add: ball_is_ground_atm is_ground_lit_def trail_defined_lit_iff_true_or_false)
  hence "scl N initial_state (trail_decide [] (Pos a), {}, None)"
    by (simp add: scl_def)
  moreover have "\<nexists>S. conflict N (trail_decide [] (Pos a), {}, None) S"
    apply (rule notI)
    apply (elim exE conflict.cases)
    using ball_is_ground_cls distinct_terms
    by (auto simp: N_def C1_def C2_def C3_def C4_def C5_def
        trail_decide_def trail_false_cls_def trail_false_lit_def)
  ultimately show "reasonable_scl N initial_state S1"
    unfolding reasonable_scl_def by (simp add: S1_def trail_decide_def)
qed


definition S2 where
  "S2 = ([
    (Pos e, None),
    (Pos a, None)], {}, None)"

lemma "regular_scl N S1 S2"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S1 S2"
    unfolding S1_def S2_def
    by (simp add: conflict.simps)
next
  have "decide N S1 S2"
    unfolding S1_def S2_def
    using distinct_terms ball_is_ground_atm
    by (auto simp: decide.simps trail_decide_def trail_defined_lit_def)
  hence "scl N S1 S2"
    unfolding scl_def by simp
  moreover have "\<nexists>S. conflict N S2 S"
    apply (rule notI)
    apply (elim exE conflict.cases)
    using ball_is_ground_cls distinct_terms
    by (auto simp add: N_def S2_def C1_def C2_def C3_def C4_def C5_def trail_false_cls_def
        trail_false_lit_def)
  ultimately show "reasonable_scl N S1 S2"
    unfolding reasonable_scl_def by simp
qed


definition S3 :: "('f, 'v) state" where
  "S3 = ([
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, None)"

lemma "regular_scl N S2 S3"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S2 S3"
    unfolding S2_def S3_def
    by (simp add: conflict.simps)
next
  have "propagate N S2 S3"
    unfolding S2_def S3_def
    unfolding propagate.simps
    apply (rule exI[of _ C1])
    using distinct_terms ball_is_ground_cls ball_is_ground_atm
    by (auto simp add: N_def C1_def trail_propagate_def is_ground_cls_def trail_false_cls_def
        trail_false_lit_def trail_defined_lit_def)
  hence "scl N S2 S3"
    unfolding scl_def by simp
  moreover have "\<nexists>S. conflict N S3 S"
    apply (rule notI)
    apply (elim exE conflict.cases)
    using ball_is_ground_cls distinct_terms
    by (auto simp add: N_def S3_def C1_def C2_def C3_def C4_def C5_def trail_false_cls_def
        trail_false_lit_def)
  ultimately show "reasonable_scl N S2 S3"
    unfolding reasonable_scl_def by simp
qed


definition S4 :: "('f, 'v) state" where
  "S4 = ([
    (Pos c, Some ({#Neg a#}, Pos c, Var)),
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, None)"

lemma "regular_scl N S3 S4"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S3 S4"
    unfolding S3_def S4_def
    by (simp add: conflict.simps)
next
  have "propagate N S3 S4"
    unfolding S3_def S4_def
    unfolding propagate.simps
    apply (rule exI[of _ C2])
    using distinct_terms ball_is_ground_cls ball_is_ground_atm
    by (auto simp add: N_def C2_def trail_propagate_def is_ground_cls_def trail_false_cls_def
        trail_false_lit_def trail_defined_lit_def)
  hence "scl N S3 S4"
    unfolding scl_def by simp
  moreover have "decide N S3 S4 \<Longrightarrow> \<nexists>S. conflict N S4 S"
    using \<open>propagate N S3 S4\<close> decide_well_defined(1) by blast
  ultimately show "reasonable_scl N S3 S4"
    unfolding reasonable_scl_def by simp
qed


definition S5 :: "('f, 'v) state" where
  "S5 = ([
    (Pos d, Some ({#Neg b#}, Pos d, Var)),
    (Pos c, Some ({#Neg a#}, Pos c, Var)),
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, None)"

lemma "regular_scl N S4 S5"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S4 S5"
    unfolding S4_def S5_def
    by (simp add: conflict.simps)
next
  have "propagate N S4 S5"
    unfolding S4_def S5_def
    unfolding propagate.simps
    apply (rule exI[of _ C3])
    using distinct_terms ball_is_ground_cls ball_is_ground_atm
    by (auto simp add: N_def C3_def trail_propagate_def is_ground_cls_def trail_false_cls_def
        trail_false_lit_def trail_defined_lit_def)
  hence "scl N S4 S5"
    unfolding scl_def by simp
  moreover have "decide N S4 S5 \<Longrightarrow> \<nexists>S. conflict N S5 S"
    using \<open>propagate N S4 S5\<close> decide_well_defined(1) by blast
  ultimately show "reasonable_scl N S4 S5"
    unfolding reasonable_scl_def by simp
qed


definition S6 :: "('f, 'v) state" where
  "S6 = ([
    (Pos d, Some ({#Neg b#}, Pos d, Var)),
    (Pos c, Some ({#Neg a#}, Pos c, Var)),
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, Some (C4, Var))"

lemma "regular_scl N S5 S6"
proof (unfold regular_scl_def, rule disjI1)
  show "conflict N S5 S6"
    unfolding S5_def S6_def
    using ball_is_ground_cls
    apply (simp add: conflict.simps N_def)
    apply (rule exI[of _ C4])
    by (simp add: C4_def trail_false_cls_def trail_false_lit_def)
qed


definition S7 :: "('f, 'v) state" where
  "S7 = ([
    (Pos d, Some ({#Neg b#}, Pos d, Var)),
    (Pos c, Some ({#Neg a#}, Pos c, Var)),
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, Some ({#Neg c, Neg b#}, Var))"

lemma "regular_scl N S6 S7"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S6 S7"
    unfolding S6_def S7_def
    by (simp add: conflict.simps)
next
  have "resolve N S6 S7"
    unfolding S6_def S7_def C4_def
    unfolding resolve.simps
    apply (rule exI[of _ "state_trail S6"])
    apply (rule exI[of _ "state_trail S4"])
    apply (rule exI[of _ "Pos d"])
    apply (rule exI[of _ "{#Neg b#}"])
    apply (rule exI[of _ Var])
    apply (rule exI[of _ "{#Neg c#}"])
    apply (rule exI[of _ Var])
    apply (rule exI[of _ "renaming_wrt
        (N \<union> clss_of_trail (state_trail S6) \<union>
         {{#Neg c#} + {#Neg d#}})"])
    apply (rule exI[of _ "{}"])
    apply (rule exI[of _ "Neg d"])
    apply (rule exI[of _ Var])
    apply (intro conjI)
          apply (simp add: S6_def)
         apply (simp add: S6_def)
         apply (rule conjI)
    using ball_is_ground_atm apply simp
    using ball_is_ground_atm apply (simp add: is_ground_atm_iff_vars_empty)
        apply (simp add: S4_def S6_def trail_propagate_def)
       apply (simp add: S6_def trail_propagate_def is_decision_lit_def trail_level_cls_def)
      apply simp
     apply simp
    by (simp del: Unification.mgu.simps add: mgu_same)
  hence "scl N S6 S7"
    unfolding scl_def by simp
  moreover have "decide N S6 S7 \<Longrightarrow> \<nexists>S. conflict N S7 S"
    using \<open>resolve N S6 S7\<close> decide_well_defined by blast
  ultimately show "reasonable_scl N S6 S7"
    unfolding reasonable_scl_def by simp
qed


definition S8 :: "('f, 'v) state" where
  "S8 = ([
    (Pos c, Some ({#Neg a#}, Pos c, Var)),
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, Some ({#Neg c, Neg b#}, Var))"

lemma "regular_scl N S7 S8"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S7 S8"
    unfolding S7_def S8_def
    by (simp add: conflict.simps)
next
  have "skip N S7 S8"
    unfolding S7_def S8_def
    using distinct_terms
    by (auto simp add: skip.simps trail_propagate_def)
  hence "scl N S7 S8"
    unfolding scl_def by simp
  moreover have "decide N S7 S8 \<Longrightarrow> \<nexists>S. conflict N S8 S"
    using \<open>skip N S7 S8\<close> decide_well_defined by blast
  ultimately show "reasonable_scl N S7 S8"
    unfolding reasonable_scl_def by simp
qed


definition S9 :: "('f, 'v) state" where
  "S9 = ([
    (Pos c, Some ({#Neg a#}, Pos c, Var)),
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, Some ({#Neg a, Neg b#}, Var))"

lemma "regular_scl N S8 S9"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S8 S9"
    unfolding S8_def S9_def
    by (simp add: conflict.simps)
next
  have "resolve N S8 S9"
    unfolding S8_def S9_def
    unfolding resolve.simps
    apply (rule exI[of _ "state_trail S4"])
    apply (rule exI[of _ "state_trail S3"])
    apply (rule exI[of _ "Pos c"])
    apply (rule exI[of _ "{#Neg a#}"])
    apply (rule exI[of _ Var])
    apply (rule exI[of _ "{#Neg b#}"])
    apply (rule exI[of _ Var])
    apply (rule exI[of _ "renaming_wrt
        (N \<union> clss_of_trail (state_trail S4) \<union>
         {{#Neg b#} + {#Neg c#}})"])
    apply (rule exI[of _ "{}"])
    apply (rule exI[of _ "Neg c"])
    apply (rule exI[of _ Var])
    apply (intro conjI)
          apply (simp add: S4_def)
    using ball_is_ground_atm apply (simp add: S4_def is_ground_atm_iff_vars_empty)
    by (simp_all del: Unification.mgu.simps
          add: S4_def S3_def trail_propagate_def is_decision_lit_def trail_level_cls_def mgu_same
          is_ground_atm_iff_vars_empty)
  hence "scl N S8 S9"
    unfolding scl_def by simp
  moreover have "decide N S8 S9 \<Longrightarrow> \<nexists>S. conflict N S9 S"
    using \<open>resolve N S8 S9\<close> decide_well_defined by blast
  ultimately show "reasonable_scl N S8 S9"
    unfolding reasonable_scl_def by simp
qed


definition S10 :: "('f, 'v) state" where
  "S10 = ([
    (Pos b, Some ({#Neg a#}, Pos b, Var)),
    (Pos e, None),
    (Pos a, None)], {}, Some ({#Neg a, Neg b#}, Var))"

lemma "regular_scl N S9 S10"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S9 S10"
    unfolding S9_def S10_def
    by (simp add: conflict.simps)
next
  have "skip N S9 S10"
    unfolding S9_def S10_def
    using distinct_terms
    by (auto simp add: skip.simps trail_propagate_def)
  hence "scl N S9 S10"
    unfolding scl_def by simp
  moreover have "decide N S9 S10 \<Longrightarrow> \<nexists>S. conflict N S10 S"
    using \<open>skip N S9 S10\<close> decide_well_defined by blast
  ultimately show "reasonable_scl N S9 S10"
    unfolding reasonable_scl_def by simp
qed


definition S11 :: "('f, 'v) state" where
  "S11 = ([(Pos a, None)], {{#Neg a, Neg b#}}, None)"

lemma "regular_scl N S10 S11"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S10 S11"
    unfolding S10_def S11_def
    by (simp add: conflict.simps)
next
  have "backtrack N S10 S11"
    unfolding S10_def S11_def
    unfolding backtrack.simps
    apply (rule exI[of _ "state_trail S3"])
    apply (rule exI[of _ "{#Neg a#}"])
    apply (rule exI[of _ Var])
    apply (rule exI[of _ "Neg b"])
    apply (rule exI[of _ "{}"])
    using distinct_terms
    by (auto simp add: S3_def is_decision_lit_def trail_level_cls_def)
  hence "scl N S10 S11"
    unfolding scl_def by simp
  moreover have "decide N S10 S11 \<Longrightarrow> \<nexists>S. conflict N S11 S"
    using \<open>backtrack N S10 S11\<close> decide_well_defined by blast
  ultimately show "reasonable_scl N S10 S11"
    unfolding reasonable_scl_def by simp
qed


definition S12 :: "('f, 'v) state" where
  "S12 =
    (let \<Gamma> = [(Pos a, None)]; U = {{#Neg a, Neg b#}} in
    (\<Gamma>, U, Some (rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) {#Neg a, Neg b#}, Var)))"

lemma "regular_scl N S11 S12"
proof (unfold regular_scl_def, rule disjI1)
  have "is_ground_cls {#Neg a, Neg b#}"
    using ball_is_ground_cls unfolding N_def C1_def
    by (metis insertCI is_ground_cls_iff_vars_empty literal.sel(1) literal.sel(2) vars_cls_add_mset)
  show "conflict N S11 S12"
    unfolding S11_def S12_def
    unfolding conflict.simps
    apply (rule exI[of _ "{#Neg a, Neg b#}"])
    apply (simp add: Let_def)
    apply (rule conjI)
     apply (metis (no_types, lifting) C1_def N_def ball_is_ground_cls insertCI
        is_ground_cls_iff_vars_empty literal.sel(1) literal.sel(2) rename_clause_ident_if_ground
        vars_cls_add_mset)
    using \<open>is_ground_cls {#Neg a, Neg b#}\<close>
    apply simp
    apply (simp add: trail_false_cls_def trail_false_lit_def)
    oops

end

end