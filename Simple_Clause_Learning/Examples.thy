theory Examples
  imports Simple_Clause_Learning
begin

(* locale example1 = scl renaming_vars inv_renaming_vars
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

end *)

locale exampl2 = scl renaming_vars inv_renaming_vars
  for renaming_vars inv_renaming_vars :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v" +
  fixes P Q R :: "('f, 'v) term"
  assumes distinct_terms: "distinct [P, Q, R]" and
    ball_is_ground_atm: "\<forall>t \<in> {P, Q, R}. is_ground_atm t"
begin

definition C1 :: "('f, 'v) term clause" where
  "C1 = {#Pos P#}"

definition C2 :: "('f, 'v) term clause" where
  "C2 = {#Pos Q#}"

definition C3 :: "('f, 'v) term clause" where
  "C3 = {#Neg P, Pos R#}"

definition C4 :: "('f, 'v) term clause" where
  "C4 = {#Neg Q, Neg R#}"

definition N :: "('f, 'v) term clause set" where
  "N = {C1, C2, C3, C4}"

lemma ball_is_ground_cls: "\<forall>C \<in> N. is_ground_cls C"
  using ball_is_ground_atm
  by (simp add: N_def C1_def C2_def C3_def C4_def is_ground_cls_def is_ground_lit_def)


definition S1 where
  "S1 = ([(Pos P, None)], {}, None)"

lemma "regular_scl N initial_state S1"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N initial_state S1"
    unfolding S1_def
    by (simp add: conflict.simps)
next
  have "decide N initial_state (trail_decide [] (Pos P), {}, None)"
    by (rule decideI)
      (simp_all add: ball_is_ground_atm is_ground_lit_def trail_defined_lit_iff_true_or_false)
  hence "scl N initial_state (trail_decide [] (Pos P), {}, None)"
    by (simp add: scl_def)
  moreover have "\<nexists>S. conflict N (trail_decide [] (Pos P), {}, None) S"
    apply (rule notI)
    apply (elim exE conflict.cases)
    using ball_is_ground_cls distinct_terms
    by (auto simp: N_def C1_def C2_def C3_def C4_def
        trail_decide_def trail_false_cls_def trail_false_lit_def)
  ultimately show "reasonable_scl N initial_state S1"
    unfolding reasonable_scl_def by (simp add: S1_def trail_decide_def)
qed


definition S2 where
  "S2 = ([
    (Pos Q, None),
    (Pos P, None)], {}, None)"

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
    by (auto simp add: N_def S2_def C1_def C2_def C3_def C4_def trail_false_cls_def
        trail_false_lit_def)
  ultimately show "reasonable_scl N S1 S2"
    unfolding reasonable_scl_def by simp
qed


definition S3 :: "('f, 'v) state" where
  "S3 = ([
    (Pos R, Some ({#Neg P#}, Pos R, Var)),
    (Pos Q, None),
    (Pos P, None)], {}, None)"

lemma "scl N S2 S3"
proof -
  have "propagate N S2 S3"
    unfolding S2_def S3_def
    unfolding propagate.simps
    apply (rule exI[of _ C3])
    using distinct_terms ball_is_ground_cls ball_is_ground_atm
    by (auto simp add: N_def C1_def C2_def C3_def trail_propagate_def is_ground_cls_def trail_false_cls_def
        trail_false_lit_def trail_defined_lit_def)
  thus "scl N S2 S3"
    unfolding scl_def by simp
qed


definition S4 :: "('f, 'v) state" where
  "S4 = ([
    (Pos R, Some ({#Neg P#}, Pos R, Var)),
    (Pos Q, None),
    (Pos P, None)], {}, Some (C4, Var))"

lemma "scl N S3 S4"
proof -
  have "conflict N S3 S4"
    unfolding S3_def S4_def
    unfolding conflict.simps
    apply (rule exI[of _ C4])
    using distinct_terms ball_is_ground_cls ball_is_ground_atm
    by (simp add: N_def trail_false_cls_def C4_def trail_false_lit_def)
  thus ?thesis
    by (simp add: scl_def)
qed


definition S5 :: "('f, 'v) state" where
  "S5 = ([
    (Pos R, Some ({#Neg P#}, Pos R, Var)),
    (Pos Q, None),
    (Pos P, None)], {}, Some ({#Neg P, Neg Q#}, Var))"

lemma "scl N S4 S5"
proof -
  have "resolve N S4 S5"
    unfolding S4_def S5_def
    unfolding resolve.simps
    apply (rule exI[of _ "state_trail S4"])
    apply (rule exI[of _ "tl (state_trail S4)"])
    (* using S4_def C4_def *)
    apply (rule exI[of _ "Pos R"])
    apply (rule exI[of _ "{#Neg P#}"])
    apply (rule exI[of _ Var])
    apply (rule exI[of _ "renaming_wrt (N \<union> clss_of_trail (fst S4) \<union> {{#Neg Q#} + {#Neg P#}})"])
    apply (rule exI[of _ "{}"])
    apply (rule exI[of _ "{#Neg Q#}"])
    apply (rule exI[of _ "Neg R"])
    apply (rule exI[of _ Var])
    apply (rule exI[of _ Var])
    using distinct_terms ball_is_ground_cls ball_is_ground_atm
    by (simp add: S4_def is_decision_lit_def C4_def trail_propagate_def trail_level_cls_def is_ground_atm_iff_vars_empty)
  thus ?thesis
    by (simp add: scl_def)
qed

lemma "grounding_of_clss N \<TTurnstile>e grounding_of_clss {{#Neg P, Neg Q#}}"
proof -
  have "is_ground_cls {#Neg P, Neg Q#}"
    using ball_is_ground_cls
    by (simp add: N_def C1_def C2_def is_ground_cls_def is_ground_lit_def)
  hence "grounding_of_clss {{#Neg P, Neg Q#}} = {{#Neg P, Neg Q#}}"
    by (simp add: grounding_of_cls_ground)

  have "grounding_of_clss N = {C1, C2, C3, C4}"
    using ball_is_ground_cls
    unfolding N_def C1_def C2_def C3_def C4_def
    by (auto simp add: grounding_of_clss_def grounding_of_cls_ground)

  show ?thesis
    unfolding \<open>grounding_of_clss N = {C1, C2, C3, C4}\<close>
    unfolding \<open>grounding_of_clss {{#Neg P, Neg Q#}} = {{#Neg P, Neg Q#}}\<close>
    unfolding C1_def C2_def C3_def C4_def
  proof (intro allI impI)
    fix I
    assume "I \<TTurnstile>s {{#Pos P#}, {#Pos Q#}, {#Neg P, Pos R#}, {#Neg Q, Neg R#}}"
    hence "P \<in> I \<and> Q \<in> I \<and> R \<in> I \<and> R \<notin> I"
      by blast
    hence False by simp
    thus "I \<TTurnstile>s {{#Neg P, Neg Q#}}" by simp
  qed
qed


definition S6 :: "('f, 'v) state" where
  "S6 = ([
    (Pos Q, None),
    (Pos P, None)], {}, Some ({#Neg P, Neg Q#}, Var))"

lemma "scl N S5 S6"
proof -
  have "skip N S5 S6"
    unfolding S5_def S6_def skip.simps
    using distinct_terms by (auto simp add: trail_propagate_def)
  thus ?thesis
    by (simp add: scl_def)
qed

lemma "\<nexists>S7. scl N S6 S7"
proof (rule notI, unfold scl_def, elim exE disjE)
  fix S7
  show "propagate N S6 S7 \<Longrightarrow> False"
    unfolding S6_def propagate.simps by simp
next
  fix S7
  show "decide N S6 S7 \<Longrightarrow> False"
    unfolding S6_def decide.simps by simp
next
  fix S7
  show "conflict N S6 S7 \<Longrightarrow> False"
    unfolding S6_def conflict.simps by simp
next
  fix S7
  show "skip N S6 S7 \<Longrightarrow> False"
    unfolding S6_def skip.simps by (simp add: trail_propagate_def)
next
  fix S7
  show "factorize N S6 S7 \<Longrightarrow> False"
    unfolding S6_def factorize.simps
    using distinct_terms
    apply (simp add: trail_propagate_def)
    apply (elim exE)
    by (metis (no_types, opaque_lifting) add_eq_conv_ex add_mset_eq_single literal.sel(2))
next
  fix S7
  show "resolve N S6 S7 \<Longrightarrow> False"
    unfolding S6_def resolve.simps by (simp add: trail_propagate_def)
next
  fix S7
  show "backtrack N S6 S7 \<Longrightarrow> False"
    oops

end

locale exampl3 = scl renaming_vars inv_renaming_vars
  for renaming_vars inv_renaming_vars :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v" +
  fixes P Q R S :: 'f and v w x y z :: 'v and a b :: "('f, 'v) term"
  assumes
    distinct_preds: "distinct [P, Q, R, S]" and
    distinct_vars: "distinct [v, w, x, y, z]" and
    distinct_terms: "distinct [a, b]" and
    ground_a[simp]: "is_ground_atm a" and
    ground_b[simp]: "is_ground_atm b"
begin

lemma ground_Fun[simp]: "\<And>f a. is_ground_atm a \<Longrightarrow> is_ground_atm (Fun f [a])"
  unfolding is_ground_atm_iff_vars_empty by simp

definition N :: "('f, 'v) term clause set" where
  "N = {
    {#Pos (Fun P [Var x])#},
    {#Pos (Fun Q [Var y])#},
    {#Neg (Fun Q [Var z]), Pos (Fun R [Var z])#},
    {#Neg (Fun R [Var w]), Pos (Fun S [Var w])#},
    {#Neg (Fun P [Var v]), Neg (Fun S [Var v])#}}"

definition S1 :: "('f, 'v) state"  where
  "S1 = ([(Pos (Fun P [a]), None)], {}, None)"

lemma "regular_scl N initial_state S1"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N initial_state S1"
    unfolding S1_def
    by (simp add: conflict.simps)
next
  have "decide N initial_state (trail_decide [] (Pos (Fun P [a])), {}, None)"
    by (rule decideI) simp_all
  hence "scl N initial_state S1"
    by (simp add: S1_def scl_def trail_decide_def)
  moreover have "\<nexists>S. conflict N S1 S"
  proof (rule notI, erule exE)
    fix S
    assume "conflict N S1 S"
    thus False
      unfolding S1_def
      apply (cases rule: conflict.cases)
      unfolding N_def Un_empty_right insert_iff
      apply (elim disjE)
      using distinct_preds
      by (simp_all add: rename_clause_def clss_of_trail_def trail_false_cls_def
          trail_false_lit_def subst_lit_def)
  qed
  ultimately show "reasonable_scl N initial_state S1"
    unfolding reasonable_scl_def by (simp add: S1_def)
qed

definition S2 :: "('f, 'v) state"  where
  "S2 = ([
    (Pos (Fun Q [a]), None),
    (Pos (Fun P [a]), None)], {}, None)"

lemma "regular_scl N S1 S2"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S1 S2"
    unfolding S1_def S2_def
    by (simp add: conflict.simps)
next
  have "decide N S1 (trail_decide (state_trail S1) (Pos (Fun Q [a])), {}, None)"
    unfolding S1_def state_trail_simp
    using distinct_preds by (auto simp: trail_defined_lit_def intro: decideI)
  hence "scl N S1 S2"
    by (simp add: S1_def S2_def scl_def trail_decide_def)
  moreover have "\<nexists>S. conflict N S2 S"
  proof (rule notI, erule exE)
    fix S
    assume "conflict N S2 S"
    thus False
      unfolding S2_def
      apply (cases rule: conflict.cases)
      unfolding N_def Un_empty_right insert_iff
      apply (elim disjE)
      using distinct_preds
      by (auto simp add: rename_clause_def clss_of_trail_def trail_false_cls_def
          trail_false_lit_def subst_lit_def)
  qed
  ultimately show "reasonable_scl N S1 S2"
    unfolding reasonable_scl_def by (simp add: S1_def)
qed

definition S3 :: "('f, 'v) state"  where
  "S3 = ([
    (Pos (Fun P [b]), None),
    (Pos (Fun Q [a]), None),
    (Pos (Fun P [a]), None)], {}, None)"

lemma "regular_scl N S2 S3"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S2 S3"
    unfolding S2_def S3_def
    by (simp add: conflict.simps)
next
  have "decide N S2 (trail_decide (state_trail S2) (Pos (Fun P [b])), {}, None)"
    unfolding S2_def state_trail_simp
    using distinct_preds distinct_terms by (auto simp: trail_defined_lit_def intro: decideI)
  hence "scl N S2 S3"
    by (simp add: S2_def S3_def scl_def trail_decide_def)
  moreover have "\<nexists>S. conflict N S3 S"
  proof (rule notI, erule exE)
    fix S
    assume "conflict N S3 S"
    thus False
      unfolding S3_def
      apply (cases rule: conflict.cases)
      unfolding N_def Un_empty_right insert_iff
      apply (elim disjE)
      using distinct_preds
      by (auto simp add: rename_clause_def clss_of_trail_def trail_false_cls_def
          trail_false_lit_def subst_lit_def)
  qed
  ultimately show "reasonable_scl N S2 S3"
    unfolding reasonable_scl_def by (simp add: S1_def)
qed

definition S4 :: "('f, 'v) state"  where
  "S4 = ([
    (Pos (Fun Q [b]), None),
    (Pos (Fun P [b]), None),
    (Pos (Fun Q [a]), None),
    (Pos (Fun P [a]), None)], {}, None)"

lemma "regular_scl N S3 S4"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S3 S4"
    unfolding S3_def S4_def
    by (simp add: conflict.simps)
next
  have "decide N S3 (trail_decide (state_trail S3) (Pos (Fun Q [b])), {}, None)"
    unfolding S3_def state_trail_simp
    using distinct_preds distinct_terms by (auto simp: trail_defined_lit_def intro: decideI)
  hence "scl N S3 S4"
    by (simp add: S3_def S4_def scl_def trail_decide_def)
  moreover have "\<nexists>S. conflict N S4 S"
  proof (rule notI, erule exE)
    fix S
    assume "conflict N S4 S"
    thus False
      unfolding S4_def
      apply (cases rule: conflict.cases)
      unfolding N_def Un_empty_right insert_iff
      apply (elim disjE)
      using distinct_preds
      by (auto simp add: rename_clause_def clss_of_trail_def trail_false_cls_def
          trail_false_lit_def subst_lit_def)
  qed
  ultimately show "reasonable_scl N S3 S4"
    unfolding reasonable_scl_def by (simp add: S1_def)
qed

abbreviation renaming_vars5 where
  "renaming_vars5 \<equiv> renaming_vars (\<Union> (vars_cls ` N))"

definition S5 :: "('f, 'v) state" where
  "S5 = ([
    (Pos (Fun R [b]), Some ({#Neg (Fun Q [Var z]) \<cdot>l (Var o renaming_vars5)#},
      Pos (Fun R [Var z]) \<cdot>l (Var o renaming_vars5), Var(renaming_vars5 z := b))),
    (Pos (Fun Q [b]), None),
    (Pos (Fun P [b]), None),
    (Pos (Fun Q [a]), None),
    (Pos (Fun P [a]), None)], {}, None)"

lemma "regular_scl N S4 S5"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S4 S5"
    unfolding S4_def S5_def
    by (simp add: conflict.simps)
next
  have "propagate N S4
    (trail_propagate (state_trail S4) (Pos (Fun R [Var z]) \<cdot>l renaming_wrt N)
      {#Neg (Fun Q [Var z]) \<cdot>l renaming_wrt N#} (Var(renaming_vars (\<Union> (vars_cls ` N)) z := b)),
      {}, None)"
    unfolding S4_def state_trail_simp
    apply (rule propagateI[of "{#Neg (Fun Q [Var z]), Pos (Fun R [Var z])#}"])
         apply (simp add: N_def)
        apply (simp add: clss_of_trail_def rename_clause_def)
       apply (auto simp add: subst_domain_def) []
      apply (simp add: is_ground_cls_def subst_lit_def)
     apply (simp add: trail_false_cls_def trail_false_lit_def subst_lit_def)
    using distinct_preds distinct_terms
    apply (auto simp add: trail_defined_lit_def subst_lit_def) []
    done
  hence "scl N S4 S5"
    by (simp add: S4_def S5_def scl_def trail_propagate_def subst_lit_def)
  moreover have "\<not> decide N S4 S5"
    by (smt (verit, ccfv_SIG) S5_def decide.cases list.inject option.discI snd_conv state_trail_simp
        trail_decide_def)
  ultimately show "reasonable_scl N S4 S5"
    unfolding reasonable_scl_def by simp
qed

abbreviation renaming_vars6 where
  "renaming_vars6 \<equiv> renaming_vars (insert (renaming_vars (\<Union> (vars_cls ` N)) z) (\<Union> (vars_cls ` N)))"

definition S6 :: "('f, 'v) state" where
  "S6 = ([
    (Pos (Fun S [b]), Some (
      {#Neg (Fun R [Var w]) \<cdot>l (Var o renaming_vars6)#},
      Pos (Fun S [Var w]) \<cdot>l (Var o renaming_vars6),
      Var(renaming_vars6 w := b))),
    (Pos (Fun R [b]), Some ({#Neg (Fun Q [Var z]) \<cdot>l (Var o renaming_vars5)#},
      Pos (Fun R [Var z]) \<cdot>l (Var o renaming_vars5), Var(renaming_vars5 z := b))),
    (Pos (Fun Q [b]), None),
    (Pos (Fun P [b]), None),
    (Pos (Fun Q [a]), None),
    (Pos (Fun P [a]), None)], {}, None)"

lemma state_trail_S6_conv: "state_trail S6 = trail_propagate (state_trail S5)
  (Pos (Fun S [Var w]) \<cdot>l (Var o renaming_vars6))
  {#Neg (Fun R [Var w]) \<cdot>l (Var o renaming_vars6)#}
  (Var(renaming_vars6 w := b))"
    by (simp add: S5_def S6_def N_def trail_propagate_def subst_lit_def)

lemma "regular_scl N S5 S6"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S5 S6"
    unfolding S5_def S6_def
    by (simp add: conflict.simps)
next
  have "propagate N S5 S6"
    unfolding S5_def S6_def state_trail_S6_conv[unfolded S6_def state_trail_simp]
    unfolding state_trail_simp
    apply (rule propagateI[of "{#Neg (Fun R [Var w]), Pos (Fun S [Var w])#}"])
         apply (simp add: N_def)
        apply (simp add: clss_of_trail_def rename_clause_def)
       apply (auto simp add: subst_domain_def) []
      apply (simp add: is_ground_cls_def subst_lit_def)
     apply (simp add: trail_false_cls_def trail_false_lit_def subst_lit_def)
    using distinct_preds distinct_terms
    apply (auto simp add: trail_defined_lit_def subst_lit_def) []
    done
  hence "scl N S5 S6"
    by (simp add: scl_def)
  moreover have "\<not> decide N S5 S6"
    by (smt (verit, del_insts) Pair_inject S6_def decide.cases list.inject option.discI
        trail_decide_def)
  ultimately show "reasonable_scl N S5 S6"
    unfolding reasonable_scl_def by simp
qed

abbreviation renaming_vars7 where
  "renaming_vars7 \<equiv> renaming_vars {v, w, z, y, x,
    renaming_vars {renaming_vars {v, w, z, y, x} z, v, w, z, y, x} w,
    renaming_vars {v, w, z, y, x} z}"

definition S7 :: "('f, 'v) state" where
  "S7 = (state_trail S6, {}, Some (
    {#Neg (Fun P [Var v]), Neg (Fun S [Var v])#} \<cdot> (Var o renaming_vars7),
    Var(renaming_vars7 v := b)))"

lemma "regular_scl N S6 S7"
proof (unfold regular_scl_def, rule disjI1)
  show "conflict N S6 S7"
    unfolding S6_def S7_def
    apply simp
    apply (rule conflictI[of "{#Neg (Fun P [Var v]), Neg (Fun S [Var v])#}"])
        apply (simp add: N_def)
       apply (simp add: rename_clause_def clss_of_trail_def N_def)
      apply (auto simp: subst_domain_def) []
    using ground_b
     apply (simp add: is_ground_cls_def subst_lit_def)
    by (simp add: trail_false_cls_def trail_false_lit_def subst_lit_def)
qed

definition renaming_wrt8 where
  "renaming_wrt8 \<equiv> renaming_wrt
    (N \<union> clss_of_trail (state_trail S6) \<union>
      {{#Neg (Fun P [Var v]), Neg (Fun S [Var v])#} \<cdot> (Var \<circ> renaming_vars7)})"

definition mgu8 where
  "mgu8 \<equiv> the (Unification.mgu
    (atm_of (Pos (Fun S [Var w]) \<cdot>l (Var \<circ> renaming_vars6)))
    (atm_of (Neg (Fun S [Var v]) \<cdot>l (Var \<circ> renaming_vars7))))"

definition conflict8 where
  "conflict8 = (
    ({#Neg (Fun P [Var v])#} \<cdot> (Var \<circ> renaming_vars7) +
     {#Neg (Fun R [Var w])#} \<cdot> (Var \<circ> renaming_vars6)) \<cdot> mgu8 \<cdot> renaming_wrt8,
    restrict_subst
      (vars_cls
        (({#Neg (Fun P [Var v])#} \<cdot> (Var \<circ> renaming_vars7) +
          {#Neg (Fun R [Var w])#} \<cdot> (Var \<circ> renaming_vars6)) \<cdot> mgu8 \<cdot> renaming_wrt8))
      (inv_renaming' renaming_wrt8 \<odot> Var(renaming_vars7 v := b) \<odot> Var(renaming_vars6 w := b)))"

definition S8 :: "('f, 'v) state" where
  "S8 = (state_trail S6, {}, Some conflict8)"

lemma "regular_scl N S7 S8"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S7 S8"
    unfolding S7_def by (simp add: conflict.simps)
next
  have "resolve N S7 S8"
    unfolding S7_def S8_def conflict8_def resolve.simps
    apply (rule exI[of _ "state_trail S6"])
    apply (rule exI[of _ "tl (state_trail S6)"])
    apply (rule exI[of _ "Pos (Fun S [Var w]) \<cdot>l (Var o renaming_vars6)"])
    apply (rule exI[of _ "{#Neg (Fun R [Var w]) \<cdot>l (Var o renaming_vars6)#}"])
    apply (rule exI[of _ "Var(renaming_vars6 w := b)"])
    apply (rule exI[of _ "renaming_wrt
        (N \<union> clss_of_trail (state_trail S6) \<union>
         {{#Neg (Fun P [Var v])#} \<cdot> (Var \<circ> renaming_vars7) +
          {#Neg (Fun S [Var v])#} \<cdot> (Var \<circ> renaming_vars7)})"])
    apply (rule exI[of _ "{}"])
    apply (rule exI[of _ "{#Neg (Fun P [Var v])#} \<cdot> (Var \<circ> renaming_vars7)"])
    apply (rule exI[of _ "Neg (Fun S [Var v]) \<cdot>l (Var \<circ> renaming_vars7)"])
    apply (rule exI[of _ "Var(renaming_vars7 v := b)"])
    apply (rule exI[of _ "the (Unification.mgu
          (atm_of
            (Pos (Fun S [Var w]) \<cdot>l
             (Var \<circ>
              renaming_vars
               (insert (renaming_vars (\<Union> (vars_cls ` N)) z)
                 (\<Union> (vars_cls ` N))))))
          (atm_of
            (Neg (Fun S [Var v]) \<cdot>l (Var \<circ> renaming_vars7))))"])
    unfolding prod.inject
    apply (intro conjI)
              apply (simp_all add: mgu8_def renaming_wrt8_def)
       apply (simp add: S6_def subst_lit_def trail_propagate_def)
    using distinct_preds apply (simp add: trail_level_cls_def subst_lit_def S6_def)
    by (simp add: decompose_def zip_option.simps subst_list_def)
  hence "scl N S7 S8"
    unfolding scl_def by simp
  moreover have "\<not> decide N S7 S8"
    unfolding S7_def
    by (simp add: decide.simps)
  ultimately show "reasonable_scl N S7 S8"
    unfolding reasonable_scl_def by simp
qed

definition S9 :: "('f, 'v) state" where
  "S9 = (state_trail S5, {}, Some conflict8)"

lemma tl_tail_propagate_def: "tl (trail_propagate \<Gamma> L C \<gamma>) = \<Gamma>"
  by (simp add: trail_propagate_def)

lemma "regular_scl N S8 S9"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S8 S9"
    unfolding S8_def by (simp add: conflict.simps)
next
  have "skip N S8 S9"
    unfolding S5_def S8_def S9_def state_trail_S6_conv state_trail_simp
    unfolding tl_tail_propagate_def
    apply (rule skipI[of _ _ "fst conflict8" "snd conflict8", unfolded prod.collapse])
    using distinct_preds
    by (auto simp add: subst_lit_def conflict8_def decompose_def zip_option.simps N_def S6_def
        clss_of_trail_def)
  hence "scl N S8 S9"
    unfolding scl_def by simp
  moreover have "\<not> decide N S8 S9"
    unfolding S8_def
    by (simp add: decide.simps)
  ultimately show "reasonable_scl N S8 S9"
    unfolding reasonable_scl_def by simp
qed

definition mgu10 where
  "mgu10 = the (Unification.mgu
          (atm_of (Pos (Fun R [Var z]) \<cdot>l renaming_wrt N))
          (atm_of
            (Neg (Fun R [Var w]) \<cdot>l
             (Var \<circ>
              renaming_vars
               (insert (renaming_vars (\<Union> (vars_cls ` N)) z)
                 (\<Union> (vars_cls ` N)))) \<cdot>l
             the (Unification.mgu
                   (atm_of
                     (Pos (Fun S [Var w]) \<cdot>l
                      (Var \<circ>
                       renaming_vars
                        (insert
                          (renaming_vars (\<Union> (vars_cls ` N)) z)
                          (\<Union> (vars_cls ` N))))))
                   (atm_of
                     (Neg (Fun S [Var v]) \<cdot>l
                      (Var \<circ> renaming_vars7)))) \<cdot>l
             renaming_wrt
              (N \<union> clss_of_trail (state_trail S6) \<union>
               {{#Neg (Fun P [Var v]), Neg (Fun S [Var v])#} \<cdot>
                (Var \<circ> renaming_vars7)}))))"

definition renaming_wrt10 where
  "renaming_wrt10 = renaming_wrt (N \<union> clss_of_trail (state_trail S5) \<union> {({#Neg (Fun P [Var v])#} \<cdot> (Var \<circ> renaming_vars7) + {#Neg (Fun R [Var w])#} \<cdot> (Var \<circ> renaming_vars6)) \<cdot> mgu8 \<cdot> renaming_wrt8})"

definition conflict_cls10 where
  "conflict_cls10 =
    ({#Neg (Fun P [Var v])#} \<cdot> (Var \<circ> renaming_vars7) \<cdot> mgu8 \<cdot> renaming_wrt8 +
     {#Neg (Fun Q [Var z])#} \<cdot> (Var \<circ> renaming_vars5)) \<cdot> mgu10 \<cdot> renaming_wrt10"

definition conflict10 where
  "conflict10 = (
    conflict_cls10,
    restrict_subst (vars_cls conflict_cls10)
      (inv_renaming' renaming_wrt10 \<odot> snd conflict8 \<odot> Var(renaming_vars5 z := b)))"

definition S10 :: "('f, 'v) state" where
  "S10 = (state_trail S5, {}, Some conflict10)"

lemma FOO: "Pos (Fun R [Var z]) \<cdot>l renaming_wrt N \<cdot>l Var
    (renaming_vars (\<Union> (vars_cls ` N)) z := b) = Pos (Fun R [b])"
  by (simp add: subst_lit_def)

lemma "regular_scl N S9 S10"
proof (unfold regular_scl_def, rule disjI2, rule conjI)
  show "\<not> conflict N S9 S10"
    unfolding S9_def by (simp add: conflict.simps)
next
  have "resolve N S9 S10"
    unfolding S9_def S10_def conflict10_def resolve.simps
    apply (rule exI[of _ "state_trail S5"])
    apply (rule exI[of _ "state_trail S4"])
    apply (rule exI[of _ "Pos (Fun R [Var z]) \<cdot>l (Var o renaming_vars5)"])
    apply (rule exI[of _ "{#Neg (Fun Q [Var z]) \<cdot>l (Var o renaming_vars5)#}"])
    apply (rule exI[of _ "Var(renaming_vars5 z := b)"])
    apply (rule exI[of _ renaming_wrt10])
    apply (rule exI[of _ "{}"])
    apply (rule exI[of _ "{#Neg (Fun P [Var v])#} \<cdot> (Var \<circ> renaming_vars7) \<cdot> mgu8 \<cdot> renaming_wrt8"])
    apply (rule exI[of _ "Neg (Fun R [Var w]) \<cdot>l (Var \<circ> renaming_vars6) \<cdot>l mgu8 \<cdot>l renaming_wrt8"])
    apply (rule exI[of _ "snd conflict8"])
    apply (rule exI[of _ mgu10])
    apply (intro conjI)
         apply (simp add: N_def decompose_def zip_option.simps S6_def clss_of_trail_def vars_cls_def
          subst_lit_def conflict8_def)
         apply (simp add: conflict_cls10_def)
       apply (simp add: S5_def S4_def trail_propagate_def subst_lit_def)
      apply (simp add: renaming_wrt10_def)
    subgoal
    unfolding FOO
     apply (simp add: subst_lit_def)
    apply (simp add: renaming_wrt8_def conflict8_def)
    sorry
  subgoal
  unfolding mgu10_def
  apply (simp add: decompose_def zip_option.simps subst_list_def S6_def)
  sorry
  oops

end

end