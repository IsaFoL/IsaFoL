theory IsaSAT_Arena_LLVM
  imports IsaSAT_Arena IsaSAT_Literals_LLVM Watched_Literals.WB_More_IICF_LLVM
begin

section \<open>Code Generation\<close>

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)

(* TODO: Let monadify-phase do this automatically? trade-of: goal-size vs. lost information *)
lemma protected_bind_assoc:
   \<open>Refine_Basic.bind$(Refine_Basic.bind$m$(\<lambda>\<^sub>2x. f x))$(\<lambda>\<^sub>2y. g y) =
    Refine_Basic.bind$m$(\<lambda>\<^sub>2x. Refine_Basic.bind$(f x)$(\<lambda>\<^sub>2y. g y))\<close> by simp


lemma convert_swap: \<open>WB_More_Refinement_List.swap = More_List.swap\<close>
  unfolding WB_More_Refinement_List.swap_def More_List.swap_def ..


subsubsection \<open>Code Generation\<close>


definition \<open>arena_el_impl_rel \<equiv> unat_rel' TYPE(32) O arena_el_rel\<close>
lemmas [fcomp_norm_unfold] = arena_el_impl_rel_def[symmetric]
abbreviation \<open>arena_el_impl_assn \<equiv> pure arena_el_impl_rel\<close>


paragraph \<open>Arena Element Operations\<close>

context
  notes [simp] = arena_el_rel_def
  notes [split] = arena_el.splits
  notes [intro!] = frefI
begin

text \<open>Literal\<close>
lemma xarena_lit_refine1: \<open>(\<lambda>eli. eli, xarena_lit) \<in> [is_Lit]\<^sub>f arena_el_rel \<rightarrow> nat_lit_rel\<close> by auto
sepref_def xarena_lit_impl [llvm_inline]
   is [] \<open>RETURN o (\<lambda>eli. eli)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = xarena_lit_impl.refine[FCOMP xarena_lit_refine1]

lemma ALit_refine1: \<open>(\<lambda>x. x,ALit) \<in> nat_lit_rel \<rightarrow> arena_el_rel\<close> by auto
sepref_def ALit_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>x. x)\<close>
  :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = ALit_impl.refine[FCOMP ALit_refine1]


text \<open>LBD\<close>

lemma xarena_lbd_refine1: \<open>(\<lambda>eli. eli >> 5, xarena_lbd) \<in> [is_Status]\<^sub>f arena_el_rel \<rightarrow> nat_rel\<close>
   by (auto simp: is_Status_def)

sepref_def xarena_lbd_impl [llvm_inline]
   is [] \<open>(RETURN o (\<lambda>eli. eli >> 5))\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

lemmas [sepref_fr_rules] = xarena_lbd_impl.refine[FCOMP xarena_lbd_refine1]

text \<open>Size\<close>
lemma xarena_length_refine1: \<open>(\<lambda>eli. eli, xarena_length) \<in> [is_Size]\<^sub>f arena_el_rel \<rightarrow> nat_rel\<close> by auto
sepref_def xarena_len_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>eli. eli)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = xarena_len_impl.refine[FCOMP xarena_length_refine1]

lemma ASize_refine1: \<open>(\<lambda>x. x,ASize) \<in> nat_rel \<rightarrow> arena_el_rel\<close> by auto
sepref_def ASize_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>x. x)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = ASize_impl.refine[FCOMP ASize_refine1]

text \<open>Position\<close>
lemma xarena_pos_refine1: \<open>(\<lambda>eli. eli, xarena_pos) \<in> [is_Pos]\<^sub>f arena_el_rel \<rightarrow> nat_rel\<close> by auto
sepref_def xarena_pos_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>eli. eli)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = xarena_pos_impl.refine[FCOMP xarena_pos_refine1]

lemma APos_refine1: \<open>(\<lambda>x. x,APos) \<in> nat_rel \<rightarrow> arena_el_rel\<close> by auto
sepref_def APos_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>x. x)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = APos_impl.refine[FCOMP APos_refine1]


text \<open>Status\<close>
definition \<open>status_impl_rel \<equiv> unat_rel' TYPE(32) O status_rel\<close>
lemmas [fcomp_norm_unfold] = status_impl_rel_def[symmetric]
abbreviation \<open>status_impl_assn \<equiv> pure status_impl_rel\<close>

lemma xarena_status_refine1: \<open>(\<lambda>eli. eli AND 0b11, xarena_status) \<in> [is_Status]\<^sub>f arena_el_rel \<rightarrow> status_rel\<close> by (auto simp: is_Status_def)
sepref_def xarena_status_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>eli. eli AND 0b11)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref
lemmas [sepref_fr_rules] = xarena_status_impl.refine[FCOMP xarena_status_refine1]

lemma xarena_used_refine1: \<open>(\<lambda>eli. (eli AND 0b1100) >> 2, xarena_used) \<in> [is_Status]\<^sub>f arena_el_rel \<rightarrow> nat_rel\<close>
  by (auto simp: is_Status_def status_rel_def bitfield_rel_def)

lemma  is_down'_32_2[simp]: \<open>is_down' UCAST(32 \<rightarrow> 2)\<close>
  by (auto simp: is_down')

lemma bitAND_mod: \<open>L AND (2^n - 1) = L mod (2^n)\<close> for L :: nat
  apply transfer
  apply (subst int_int_eq[symmetric])
  apply (subst and_nat_def)
   using AND_mod[of \<open>int _\<close>]
  apply (auto simp: zmod_int bitval_bin_last[symmetric])
  done

lemma nat_ex_numeral: \<open>\<exists>m. n=0 \<or> n = numeral m\<close> for n :: nat
  apply (induction n)
  apply auto
  using llvm_num_const_simps(67) apply blast
  using pred_numeral_inc by blast

lemma xarena_used_implI: \<open>x AND 12 >> 2 < max_unat 2\<close> for x :: nat
  using nat_ex_numeral[of x]
  by (auto simp: nat_shiftr_div nat_shifl_div numeral_eq_Suc Suc_numeral max_unat_def
        less_mult_imp_div_less
      simp flip: numeral_eq_Suc)

sepref_def xarena_used_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>eli.(eli AND 0b1100) >> 2)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE(2)\<close>
  supply [simp] = xarena_used_implI
  apply (annot_unat_const \<open>TYPE(32)\<close>)
   apply (rewrite at \<open>RETURN o (\<lambda>_. \<hole>)\<close> annot_unat_unat_downcast[where 'l=2])
  by sepref

sepref_register \<open>(=) :: clause_status \<Rightarrow> clause_status \<Rightarrow> _\<close>

lemmas [sepref_fr_rules] = xarena_used_impl.refine[FCOMP xarena_used_refine1]

lemma status_eq_refine1: \<open>((=),(=)) \<in> status_rel \<rightarrow> status_rel \<rightarrow> bool_rel\<close>
  by (auto simp: status_rel_def)

sepref_def status_eq_impl [llvm_inline] is [] \<open>uncurry (RETURN oo (=))\<close>
  :: \<open>(unat_assn' TYPE(32))\<^sup>k *\<^sub>a (unat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

lemmas [sepref_fr_rules] = status_eq_impl.refine[FCOMP status_eq_refine1]

sepref_register neq : \<open>(op_neq :: clause_status \<Rightarrow> _ \<Rightarrow> _)\<close>
lemma status_neq_refine1: \<open>((\<noteq>),op_neq) \<in> status_rel \<rightarrow> status_rel \<rightarrow> bool_rel\<close>
  by (auto simp: status_rel_def)

definition \<open>AStatus_impl1 cs used lbd \<equiv>
    (cs AND unat_const TYPE(32) 0b11) + (used << 2) + (lbd << unat_const TYPE(32) 5)\<close>

lemma bang_eq_int:
  fixes x :: "int"
  shows "(x = y) = (\<forall>n. x !! n = y !! n)"
  using bin_eqI by auto

lemma bang_eq_nat:
  fixes x :: "nat"
  shows "(x = y) = (\<forall>n. x !! n = y !! n)"
  unfolding int_int_eq[symmetric] bang_eq_int
by (simp add: bit_of_nat_iff_bit test_bit_eq_bit)

lemma sum_bitAND_shift_pow2:
  \<open>(a + (b << (n + m))) AND (2^n - 1) = a AND (2^n - 1)\<close> for a b n :: nat
  unfolding bitAND_mod
  apply (auto simp: nat_shiftr_div)
  by (metis mod_mult_self2 power_add semiring_normalization_rules(19))

lemma and_bang_nat: \<open>(x AND y) !! n = (x !! n \<and> y !! n)\<close> for x y n :: nat
  unfolding and_nat_def
  by (metis and_nat_def bit_and_iff test_bit_eq_bit)

lemma AND_12_AND_15_AND_12: \<open>a AND 12 = (a AND 15) AND 12\<close> for a :: nat
proof -
  have [simp]: \<open>(12::nat) !! n \<Longrightarrow> (15::nat) !! n\<close> for n :: nat
    by (auto simp: nat_set_bit_test_bit bin_nth_numeral_unfold
      nat_bin_nth_bl' nth_Cons split: nat.splits)
  show ?thesis
    by (subst bang_eq_nat, (subst and_bang_nat)+)
     (auto simp: and_bang_nat)
qed


lemma AStatus_shift_safe:
    \<open>c \<ge> 2 \<Longrightarrow> x42 + (x43 << c) AND 3 = x42 AND 3\<close>
    \<open>(x53 << 2) AND 3 = 0\<close>
    \<open>x42 + (x43 << 4) AND 12 = x42 AND 12\<close>
    \<open>x42 + (x43 << 5) AND 12 = x42 AND 12\<close>
    \<open>Suc (x42 + (x43 << 5)) AND 12 = (Suc x42) AND 12\<close>
    \<open>Suc ((x42) + (x43 << 5)) AND 3 = Suc x42 AND 3\<close>
    \<open>Suc (x42 << 2) AND 3 = Suc 0\<close>
    \<open>x42 \<le> 3 \<Longrightarrow> Suc ((x42 << 2) + (x43 << 5)) >> 5 = x43\<close>
   for x42 x43 x53 :: nat
proof -
  show \<open>c \<ge> 2 \<Longrightarrow> x42 + (x43 << c) AND 3 = x42 AND 3\<close>
    using sum_bitAND_shift_pow2[of x42 x43 2 \<open>c - 2\<close>]
    by auto

  show \<open>(x53 << 2) AND 3 = 0\<close>
    using bitAND_mod[of _ 2]
    by (auto simp: nat_shiftr_div)
  have 15: \<open>(15 :: nat) = 2 ^4 -1\<close> by auto
  show H: \<open>x42 + (x43 << 4) AND 12 = x42 AND 12\<close> for x42 x43 :: nat
    apply (subst AND_12_AND_15_AND_12)
    apply (subst (2) AND_12_AND_15_AND_12)
    unfolding bitAND_mod 15
    by (auto simp: nat_shiftr_div)
  from H[of x42 \<open>x43 << 1\<close>] show \<open>x42 + (x43 << 5) AND 12 = x42 AND 12\<close>
    by (auto simp: nat_shiftr_div ac_simps)
  from H[of \<open>Suc x42\<close> \<open>x43 << 1\<close>] show \<open>Suc (x42 + (x43 << 5)) AND 12 = (Suc x42) AND 12\<close>
    by (auto simp: nat_shiftr_div ac_simps)
  have [simp]: \<open>(a + x53 * 32) mod 4 = (a mod 4)\<close> for a x53 :: nat
    by (metis (no_types, lifting) add_eq_self_zero cong_exp_iff_simps(1) cong_exp_iff_simps(2)
     mod_add_eq mod_eq_nat1E mod_mult_right_eq mult_0_right order_refl)
  note [simp] = this[of \<open>Suc a\<close> for a, simplified]
  show \<open>Suc ((x42) + (x43 << 5)) AND 3 = Suc x42 AND 3\<close>
    using bitAND_mod[of _ 2]
    by (auto simp: nat_shiftr_div)
  show \<open>Suc (x42 << 2) AND 3 = Suc 0\<close>
    using bitAND_mod[of _ 2]
    by (auto simp: nat_shiftr_div mod_Suc)
  show \<open>x42 \<le> 3 \<Longrightarrow> Suc ((x42 << 2) + (x43 << 5)) >> 5 = x43\<close>
    by (auto simp: nat_shiftr_div nat_shifl_div)
qed

  (*
lemma AStatus_shift_safe: \<open>4 + (x53 << 2) AND 3 = 0\<close> \<open>(x53 << 2) AND 3 = 0\<close>
   \<open>5 + (x53 << 2) AND 3 = 1\<close> \<open>(x53 << 5) AND 3 = 0\<close>  \<open>4 + (x53 << 5) AND 3 = 0\<close>
   \<open>5 + (x53 << 5) AND 3 = Suc 0\<close> \<open>Suc (x53 << 5) AND 3 = Suc 0\<close> \<open>3 + (x53 << 5) AND 3 = 3\<close>
   \<open>7 + (x53 << 5) AND 3 = 3\<close>  \<open>(x53 << 5) AND 4 = 0\<close> \<open>4 + (x53 << 5) AND 4 = 4\<close>
   \<open>Suc (x53 << 5) AND 4 = 0\<close> \<open>3 + (x53 << 5) AND 4 = 0\<close>
   \<open>5 + (x53 << 5) AND 4 = 4\<close> \<open>7 + (x53 << 4) AND 5 = 4\<close>
   \<open>(7 :: nat) >> (4 :: nat) = 0\<close> \<open>(5 :: nat) >> (4 :: nat) = 0\<close> \<open>(4 :: nat) >> (4 :: nat) = 0\<close>
   \<open>(3 :: nat) >> (4 :: nat) = 0\<close> \<open>Suc (x53 << 5) >> 5 = x53\<close>
    \<open>x42 + (x43 << 5) AND 3 = x42 AND 3\<close>
   for x42 x43 x53 :: nat
proof -
  have [simp]: \<open>(a + x53 * 16) mod 4 = (a mod 4)\<close> for a :: nat
    by (metis (no_types, lifting) add_eq_self_zero cong_exp_iff_simps(1) cong_exp_iff_simps(2)
     mod_add_eq mod_eq_nat1E mod_mult_right_eq mult_0_right order_refl)
  from this[of \<open>Suc 0\<close>] have [simp]: \<open>Suc (x53 * 16) mod 4 = 1\<close> for a :: nat
    by auto

  show \<open>4 + (x53 << 2) AND 3 = 0\<close> \<open>(x53 << 2) AND 3 = 0\<close>
    \<open>5 + (x53 << 2) AND 3 = 1\<close> \<open>(x53 << 4) AND 3 = 0\<close>  \<open>4 + (x53 << 4) AND 3 = 0\<close>
    \<open>5 + (x53 << 4) AND 3 = Suc 0\<close> \<open>Suc (x53 << 4) AND 3 = Suc 0\<close> \<open>3 + (x53 << 4) AND 3 = 3\<close>
    \<open>7 + (x53 << 4) AND 3 = 3\<close>
    using bitAND_mod[of _ 2]
    by (auto simp: nat_shiftr_div)

  have 4: \<open>4 = Suc (Suc (Suc (Suc 0)))\<close>
    by auto
  show \<open>(x53 << 4) AND 4 = 0\<close>
    using nat_ex_numeral[of x53]
    apply (auto simp: nat_shiftr_div nat_shifl_div numeral_eq_Suc Suc_numeral
      simp flip: numeral_eq_Suc)
    apply (case_tac m)
    apply auto
    apply (case_tac x2)
    apply auto
    done
  show \<open>4 + (x53 << 4) AND 4 = 4\<close>
    using nat_ex_numeral[of x53]
    apply (auto simp: nat_shiftr_div nat_shifl_div numeral_eq_Suc Suc_numeral
      simp flip: numeral_eq_Suc)
    apply (case_tac m)
    apply auto
    apply (case_tac x2)
    apply auto
    done
  show \<open>Suc (x53 << 4) AND 4 = 0\<close>
    using nat_ex_numeral[of x53]
    apply (auto simp: nat_shiftr_div nat_shifl_div numeral_eq_Suc Suc_numeral
      simp flip: numeral_eq_Suc)
    apply (case_tac m)
    apply auto
    apply (case_tac x2)
    apply auto
    done
  show \<open>3 + (x53 << 4) AND 4 = 0\<close>
    using nat_ex_numeral[of x53]
    apply (auto simp: nat_shiftr_div nat_shifl_div numeral_eq_Suc Suc_numeral
      simp flip: numeral_eq_Suc)
    apply (case_tac m)
    apply auto
    apply (case_tac x2)
    apply auto
    done
  show \<open>5 + (x53 << 4) AND 4 = 4\<close>
    using nat_ex_numeral[of x53]
    apply (auto simp: nat_shiftr_div nat_shifl_div numeral_eq_Suc Suc_numeral
      simp flip: numeral_eq_Suc)
    apply (case_tac m)
    apply auto
    apply (case_tac x2)
    apply auto
    done
  show \<open>7 + (x53 << 4) AND 4 = 4\<close>
    using nat_ex_numeral[of x53]
    apply (auto simp: nat_shiftr_div nat_shifl_div numeral_eq_Suc Suc_numeral
      simp flip: numeral_eq_Suc)
    apply (case_tac m)
    apply auto
    apply (case_tac x2)
    apply auto
    done
  show \<open>(7 :: nat) >> (4 :: nat) = 0\<close> \<open>(5 :: nat) >> (4 :: nat) = 0\<close> \<open>(4 :: nat) >> (4 :: nat) = 0\<close>
     \<open>(3 :: nat) >> (4 :: nat) = 0\<close>
    by (auto simp: nat_shiftr_div nat_shifl_div numeral_eq_Suc Suc_numeral
      simp flip: numeral_eq_Suc)
  show \<open>Suc (x53 << 4) >> 4 = x53\<close>
    using nat_ex_numeral[of x53]
    by (auto simp: nat_shiftr_div nat_shifl_div numeral_eq_Suc Suc_numeral
      simp flip: numeral_eq_Suc)
  have H: \<open>nat (a + b) = nat a + nat b\<close> if \<open>a \<ge> 0\<close> \<open>b \<ge> 0\<close> for a b :: int
    using that by auto
  show \<open>x42 + (x43 << 4) AND 3 = x42 AND 3\<close>
    using sum_bitAND_shift_pow2[of x42 x43 2 2]
    by auto

qed
*)
lemma less_unat_AND_shift: \<open>x42 < 2^n \<Longrightarrow> x42 >> n = 0\<close> for x42 :: nat
  by (auto simp: nat_shifl_div)

lemma [simp]: \<open>(a + (w << n)) >> n = (a >> n) + w\<close> \<open>((w << n)) >> n = w\<close>
  \<open>n \<le> m \<Longrightarrow> ((w << n)) >> m = w >> (m - n)\<close> 
  \<open>n \<ge> m \<Longrightarrow> ((w << n)) >> m = w << (n - m)\<close> for w n :: nat
  apply (auto simp: nat_shiftr_div nat_shifl_div)
  apply (metis div_mult2_eq le_add_diff_inverse nonzero_mult_div_cancel_right power_add power_eq_0_iff
    zero_neq_numeral)
by (smt Groups.mult_ac(2) le_add_diff_inverse nonzero_mult_div_cancel_right power_add power_eq_0_iff semiring_normalization_rules(19) zero_neq_numeral)

lemma less_numeral_pred:
  \<open>a \<le> numeral b \<longleftrightarrow> a = numeral b \<or> a \<le> pred_numeral b\<close> for a :: nat
  by (auto simp: numeral_eq_Suc)

lemma nat_shiftl_numeral [simp]:
  "(numeral w :: nat) << numeral w' = numeral (num.Bit0 w) << pred_numeral w'"
  by (metis mult_2 nat_shiftr_div numeral_Bit0 numeral_eq_Suc power.simps(2)
    semiring_normalization_rules(18) semiring_normalization_rules(7))

lemma nat_shiftl_numeral' [simp]:
  "(numeral w :: nat) << 1 = numeral (num.Bit0 w)"
  "(1 :: nat) << n = 2 ^ n"
  using nat_shiftl_numeral[of w num.One, unfolded numeral.numeral_One]
  by (auto simp: nat_shiftr_div)

lemma shiftr_nat_alt_def: \<open>(a :: nat) >> b = nat (int a >> b)\<close>
  apply (induction b)
    apply (auto simp: nat_shiftr)
  by (smt (z3) div_div_p2_eq_div_p2s(2) int_nat_eq nat_2 nat_int.Rep_inverse' nat_shifl_div numeral_2_eq_2 semiring_1_class.of_nat_power shiftr_int_def zdiv_int)


lemma nat_shiftr_numeral [simp]:
  "(1 :: nat) >> numeral w' = 0"
  "(numeral num.One :: nat) >> numeral w' = 0"
  "(numeral (num.Bit0 w) :: nat) >> numeral w' = numeral w >> pred_numeral w'"
  "(numeral (num.Bit1 w) :: nat) >> numeral w' = numeral w >> pred_numeral w'"
  unfolding shiftr_nat_alt_def
  by auto

lemma nat_shiftr_numeral_Suc0 [simp]:
  "(1 :: nat) >> Suc 0 = 0"
  "(numeral num.One :: nat) >> Suc 0 = 0"
  "(numeral (num.Bit0 w) :: nat) >> Suc 0 = numeral w"
  "(numeral (num.Bit1 w) :: nat) >> Suc 0 = numeral w"
  unfolding shiftr_nat_alt_def
  by auto

lemma nat_shiftr_numeral1 [simp]:
  "(1 :: nat) >> 1 = 0"
  "(numeral num.One :: nat) >> 1 = 0"
  "(numeral (num.Bit0 w) :: nat) >> 1 = numeral w"
  "(numeral (num.Bit1 w) :: nat) >> 1 = numeral w"
  unfolding shiftr_nat_alt_def
  by auto

lemma nat_numeral_and_one: \<open>(1 :: nat) AND 1 = 1\<close>
  by simp

lemma AStatus_refine1: \<open>(AStatus_impl1, AStatus) \<in> status_rel \<rightarrow> br id (\<lambda>n. n \<le> 3) \<rightarrow> nat_rel \<rightarrow> arena_el_rel\<close>
  apply (auto simp: status_rel_def bitfield_rel_def AStatus_impl1_def AStatus_shift_safe br_def
      less_unat_AND_shift
    split: if_splits)
  apply (auto simp: less_numeral_pred le_Suc_eq nat_and_numerals nat_numeral_and_one;
        auto simp flip: One_nat_def)+
  done

lemma AStatus_implI:
  assumes \<open>b << 5 < max_unat 32\<close>
  shows \<open>b << 5 < max_unat 32 - 7\<close> \<open>(a AND 3) + 4 + (b << 5) < max_unat 32\<close>
    \<open>(a AND 3) + (b << 5) < max_unat 32\<close>
proof -
  show \<open>b << 5 < max_unat 32 - 7\<close>
    using assms
    by (auto simp: max_unat_def nat_shiftr_div)
  have \<open>(a AND 3) + 4 + (b << 5) \<le> 7 + (b << 5)\<close>
    using AND_upper_nat2[of 3 a]
    by auto
  also have \<open>7 + (b << 5) < max_unat 32\<close>
    using \<open>b << 5 < max_unat 32 - 7\<close> by auto
  finally show \<open>(a AND 3) + 4 + (b << 5) < max_unat 32\<close> .
  then show \<open>(a AND 3) + (b << 5) < max_unat 32\<close>
    by auto
qed

lemma nat_shiftr_mono: \<open>a < b \<Longrightarrow> a << n < b << n\<close> for a b :: nat
  by (simp add: nat_shiftr_div)

lemma AStatus_implI3:
  assumes \<open>(ac :: 2 word, ba) \<in> unat_rel\<close>
  shows \<open>(a AND (3::nat)) + (ba << (2::nat)) < max_unat (32::nat)\<close> and
    \<open>b << 5 < max_unat 32 \<Longrightarrow> (a AND 3) + (ba << 2) + (b << 5) < max_unat 32\<close>
proof -
  have \<open>ba < 4\<close>
    using assms unat_lt_max_unat[of ac] by (auto simp: unat_rel_def unat.rel_def br_def
       max_unat_def)
  from nat_shiftr_mono[OF this, of 2] have \<open>ba << 2 < 16\<close> by auto
  moreover have \<open>(a AND (3::nat)) \<le> 3\<close>
    using AND_upper_nat2[of a 3] by auto
  ultimately have \<open>(a AND (3::nat)) + (ba << (2::nat)) < 19\<close>
    by linarith
  also have \<open>19 \<le> max_unat 32\<close>
    by (auto simp: max_unat_def)
  finally show \<open>(a AND (3::nat)) + (ba << (2::nat)) < max_unat (32::nat)\<close> .

  show \<open>(a AND 3) + (ba << 2) + (b << 5) < max_unat 32\<close> if \<open>b << 5 < max_unat 32\<close>
  proof -
    have \<open>b << 5 < max_unat 32 - 19\<close>
      using that
      by (auto simp: max_unat_def nat_shiftr_div)
    then show ?thesis
      using  \<open>(a AND (3::nat)) + (ba << (2::nat)) < 19\<close> by linarith
  qed
qed

lemma AStatus_implI2: \<open>(ac :: 2 word, ba) \<in> unat_rel \<Longrightarrow> ba << (2::nat) < max_unat (32::nat)\<close>
  using order.strict_trans2[OF unat_lt_max_unat[of ac], of \<open>max_unat 28\<close>]
   by (auto simp: unat_rel_def unat.rel_def br_def max_unat_def nat_shiftr_div
      intro!: )

lemma is_up_2_32[simp]: \<open>is_up' UCAST(2 \<rightarrow> 32)\<close>
  by (simp add: is_up')

sepref_def AStatus_impl [llvm_inline] 
  is [] \<open>uncurry2 (RETURN ooo AStatus_impl1)\<close>
   :: \<open>[\<lambda>((a,b), c). c << 5 < max_unat 32]\<^sub>a
      uint32_nat_assn\<^sup>k *\<^sub>a (unat_assn' TYPE(2))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding AStatus_impl1_def
  supply [split] = if_splits and [intro] = AStatus_implI AStatus_implI2 AStatus_implI3
  apply (rewrite in \<open>\<hole> << 2\<close> annot_unat_unat_upcast[where 'l=\<open>32\<close>])
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

lemma Collect_eq_simps3: \<open>P O {(c, a). a = c \<and> Q c} = {(a, b). (a, b) \<in> P \<and> Q b}\<close>
   \<open>P O {(c, a). c = a \<and> Q c} = {(a, b). (a, b) \<in> P \<and> Q b}\<close>
  by auto

lemma unat_rel_2_br: \<open>(((unat_rel :: (2 word \<times> _) set) O br id (\<lambda>n. n \<le> 3))) = ((unat_rel))\<close>
  apply (auto simp add: unat_rel_def unat.rel_def br_def Collect_eq_simps3 max_unat_def)
  subgoal for a
     using unat_lt_max_unat[of \<open>a :: 2 word\<close>] by (auto simp: max_unat_def)
  done

lemmas [sepref_fr_rules] = AStatus_impl.refine[FCOMP AStatus_refine1, unfolded unat_rel_2_br]



subsubsection \<open>Arena Operations\<close>

paragraph \<open>Length\<close>

abbreviation \<open>arena_fast_assn \<equiv> al_assn' TYPE(64) arena_el_impl_assn\<close>

lemma arena_lengthI:
  assumes \<open>arena_is_valid_clause_idx a b\<close>
  shows \<open>Suc 0 \<le> b\<close>
  and \<open>b < length a\<close>
  and \<open>is_Size (a ! (b - Suc 0))\<close>
  using SIZE_SHIFT_def assms
  by (auto simp: arena_is_valid_clause_idx_def arena_lifting)

(*
lemma arena_length_impl_bounds_aux1:
  \<open>(ac, a) \<in> unat_rel' TYPE(32) \<Longrightarrow> a < 9223372036854775806\<close>
  by (auto dest!: in_unat_rel_imp_less_max' simp: max_unat_def)
*)

lemma arena_length_alt:
  \<open>arena_length arena i = (
    let l = xarena_length (arena!(i - snat_const TYPE(64) 1))
    in snat_const TYPE(64) 2 + op_unat_snat_upcast TYPE(64) l)\<close>
  by (simp add: arena_length_def SIZE_SHIFT_def)

sepref_register arena_length
sepref_def arena_length_impl
  is \<open>uncurry (RETURN oo arena_length)\<close>
    :: \<open>[uncurry arena_is_valid_clause_idx]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> snat_assn' TYPE(64)\<close>
  unfolding arena_length_alt
  supply [dest] = arena_lengthI
  by sepref


paragraph \<open>Literal at given position\<close>

lemma arena_lit_implI:
  assumes \<open>arena_lit_pre a b\<close>
  shows \<open>b < length a\<close> \<open>is_Lit (a ! b)\<close>
  using assms unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
  by (fastforce dest: arena_lifting)+

sepref_register arena_lit xarena_lit
sepref_def arena_lit_impl
  is \<open>uncurry (RETURN oo arena_lit)\<close>
    :: \<open>[uncurry arena_lit_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply [intro] = arena_lit_implI
  unfolding arena_lit_def
  by sepref

sepref_register mop_arena_lit mop_arena_lit2
sepref_def mop_arena_lit_impl
  is \<open>uncurry (mop_arena_lit)\<close>
    :: \<open>arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  supply [intro] = arena_lit_implI
  unfolding mop_arena_lit_def
  by sepref

sepref_def mop_arena_lit2_impl
  is \<open>uncurry2 (mop_arena_lit2)\<close>
    :: \<open>[\<lambda>((N, _), _). length N \<le> sint64_max]\<^sub>a 
          arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k  *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply [intro] = arena_lit_implI
  supply [dest] = arena_lit_pre_le_lengthD
  unfolding mop_arena_lit2_def
  by sepref



paragraph \<open>Status of the clause\<close>

lemma arena_status_implI:
  assumes \<open>arena_is_valid_clause_vdom a b\<close>
  shows \<open>2 \<le> b\<close> \<open>b - 2 < length a\<close> \<open>is_Status (a ! (b-2))\<close>
  using assms STATUS_SHIFT_def arena_dom_status_iff
  unfolding arena_is_valid_clause_vdom_def
  by (auto dest: valid_arena_in_vdom_le_arena arena_lifting)

sepref_register arena_status xarena_status
sepref_def arena_status_impl
  is \<open>uncurry (RETURN oo arena_status)\<close>
    :: \<open>[uncurry arena_is_valid_clause_vdom]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> status_impl_assn\<close>
  supply [intro] = arena_status_implI
  unfolding arena_status_def STATUS_SHIFT_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


paragraph \<open>Swap literals\<close>
sepref_register swap_lits
sepref_def swap_lits_impl is \<open>uncurry3 (RETURN oooo swap_lits)\<close>
  :: \<open>[\<lambda>(((C,i),j),arena). C + i < length arena \<and> C + j < length arena]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow> arena_fast_assn\<close>
  unfolding swap_lits_def convert_swap
  unfolding gen_swap
  by sepref


paragraph \<open>Get LBD\<close>

lemma get_clause_LBD_pre_implI:
  assumes \<open>get_clause_LBD_pre a b\<close>
  shows \<open>2 \<le> b\<close> \<open>b - 2 < length a\<close> \<open>is_Status (a ! (b-2))\<close>
  using assms arena_dom_status_iff
  unfolding arena_is_valid_clause_vdom_def get_clause_LBD_pre_def
  apply (auto dest: valid_arena_in_vdom_le_arena simp: arena_lifting arena_is_valid_clause_idx_def)
  using STATUS_SHIFT_def arena_lifting apply auto
  by (meson less_imp_diff_less)

sepref_register arena_lbd mop_arena_lbd
sepref_def arena_lbd_impl
  is \<open>uncurry (RETURN oo arena_lbd)\<close>
    :: \<open>[uncurry get_clause_LBD_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>uint32_nat_assn\<close>
  unfolding arena_lbd_def LBD_SHIFT_def
  supply [dest] = get_clause_LBD_pre_implI 
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def mop_arena_lbd_impl
  is \<open>uncurry mop_arena_lbd\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding mop_arena_lbd_def
  by sepref


paragraph \<open>used flag\<close>
sepref_register arena_used
sepref_def arena_used_impl
  is \<open>uncurry (RETURN oo arena_used)\<close>
    :: \<open>[uncurry get_clause_LBD_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_assn' TYPE(2)\<close>
  unfolding arena_used_def LBD_SHIFT_def
  supply [dest] = get_clause_LBD_pre_implI 
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

paragraph \<open>Get Saved Position\<close>


lemma arena_posI:
  assumes \<open>get_saved_pos_pre a b\<close>
  shows \<open>3 \<le> b\<close>
  and \<open>b < length a\<close>
  and \<open>is_Pos (a ! (b - 3))\<close>
  using POS_SHIFT_def assms is_short_clause_def[of \<open>_ \<propto> b\<close>]
  apply (auto simp: get_saved_pos_pre_def arena_is_valid_clause_idx_def arena_lifting
     MAX_LENGTH_SHORT_CLAUSE_def[symmetric] arena_lifting(11) arena_lifting(4)
     simp del: MAX_LENGTH_SHORT_CLAUSE_def)
  using arena_lifting(1) arena_lifting(4) header_size_def by fastforce

lemma arena_pos_alt:
  \<open>arena_pos arena i = (
    let l = xarena_pos (arena!(i - snat_const TYPE(64) 3))
    in snat_const TYPE(64) 2 + op_unat_snat_upcast TYPE(64) l)\<close>
  by (simp add: arena_pos_def POS_SHIFT_def)

sepref_register arena_pos
sepref_def arena_pos_impl
  is \<open>uncurry (RETURN oo arena_pos)\<close>
    :: \<open>[uncurry get_saved_pos_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> snat_assn' TYPE(64)\<close>
  unfolding arena_pos_alt
  supply [dest] = arena_posI
  by sepref

paragraph \<open>Update LBD\<close>

lemma update_lbdI:
  assumes \<open>update_lbd_pre ((b, lbd), a)\<close>
  shows \<open>2 \<le> b\<close>
  and \<open>b -2 < length a\<close>
  and \<open>arena_is_valid_clause_vdom a b\<close>
  and \<open>get_clause_LBD_pre a b\<close>
  using LBD_SHIFT_def assms
  apply (auto simp: arena_is_valid_clause_idx_def arena_lifting update_lbd_pre_def
        arena_is_valid_clause_vdom_def get_clause_LBD_pre_def
    dest: arena_lifting(10))
  by (simp add: less_imp_diff_less valid_arena_def)

lemma shorten_lbd_le: \<open>shorten_lbd baa << 5 < max_unat 32\<close>
proof -
  have \<open>shorten_lbd baa << 5 \<le> 67108863 << 5\<close>
    using AND_upper_nat2[of baa 67108863]
    by (auto simp: nat_shiftr_div shorten_lbd_def)
  also have \<open>67108863 << 5 < max_unat 32\<close>
    by (auto simp: max_unat_def nat_shiftr_div)
  finally show ?thesis .
qed

sepref_register update_lbd AStatus shorten_lbd
sepref_def shorten_lbd_impl
  is \<open>RETURN o shorten_lbd\<close>
    :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding shorten_lbd_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref


sepref_def update_lbd_impl
  is \<open>uncurry2 (RETURN ooo update_lbd)\<close>
    :: \<open>[update_lbd_pre]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d  \<rightarrow> arena_fast_assn\<close>
  unfolding update_lbd_def LBD_SHIFT_def
  supply [simp] = update_lbdI shorten_lbd_le
    and [dest] = arena_posI
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def mop_arena_update_lbd_impl
  is \<open>uncurry2 mop_arena_update_lbd\<close>
    :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d  \<rightarrow>\<^sub>a arena_fast_assn\<close>
  unfolding mop_arena_update_lbd_def
  by sepref



paragraph \<open>Update Saved Position\<close>

lemma update_posI:
  assumes \<open>isa_update_pos_pre ((b, pos), a)\<close>
  shows \<open>3 \<le> b\<close> \<open>2 \<le> pos\<close> \<open>b-3 < length a\<close>
  using assms POS_SHIFT_def
  unfolding isa_update_pos_pre_def
  apply (auto simp: arena_is_valid_clause_idx_def arena_lifting)
  (* TODO: Clean up this mess *)
  apply (metis (full_types) MAX_LENGTH_SHORT_CLAUSE_def arena_is_valid_clause_idx_def arena_posI(1) get_saved_pos_pre_def)
  by (simp add: less_imp_diff_less valid_arena_def)

lemma update_posI2:
  assumes \<open>isa_update_pos_pre ((b, pos), a)\<close>
  assumes \<open>rdomp (al_assn arena_el_impl_assn :: _ \<Rightarrow> (32 word, 64) array_list \<Rightarrow> assn) a\<close>
  shows \<open>pos - 2 < max_unat 32\<close>
proof -
  obtain N vdom where
    \<open>valid_arena a N vdom\<close> and
    \<open>b \<in># dom_m N\<close>
    using assms(1) unfolding isa_update_pos_pre_def arena_is_valid_clause_idx_def
    by auto
  then have eq: \<open>length (N \<propto> b) = arena_length a b\<close> and
    le: \<open>b < length a\<close> and
    size: \<open>is_Size (a ! (b - SIZE_SHIFT))\<close>
    by (auto simp: arena_lifting)

  have \<open>i<length a \<Longrightarrow> rdomp arena_el_impl_assn (a ! i)\<close> for i
    using rdomp_al_dest'[OF assms(2)]
    by auto
  from this[of \<open>b - SIZE_SHIFT\<close>] have \<open>rdomp arena_el_impl_assn (a ! (b - SIZE_SHIFT))\<close>
    using le by auto
  then have \<open>length (N \<propto> b) \<le> uint32_max + 2\<close>
    using size eq unfolding rdomp_pure
    apply (auto simp: rdomp_def arena_el_impl_rel_def is_Size_def
       comp_def pure_def unat_rel_def unat.rel_def br_def
       arena_length_def uint32_max_def)
     subgoal for x
       using unat_lt_max_unat[of x]
       apply (auto simp: max_unat_def)
       done
    done
  then show ?thesis
    using assms POS_SHIFT_def
    unfolding isa_update_pos_pre_def
    by (auto simp: arena_is_valid_clause_idx_def arena_lifting eq
       uint32_max_def max_unat_def)
qed

sepref_register arena_update_pos
sepref_def update_pos_impl
  is \<open>uncurry2 (RETURN ooo arena_update_pos)\<close>
    :: \<open>[isa_update_pos_pre]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d  \<rightarrow> arena_fast_assn\<close>
  unfolding arena_update_pos_def POS_SHIFT_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply (rewrite at \<open>APos \<hole>\<close> annot_snat_unat_downcast[where 'l=32])
  supply [simp] = update_posI and [dest] = update_posI2
  by sepref


sepref_register IRRED LEARNED DELETED
lemma IRRED_impl[sepref_import_param]: \<open>(0,IRRED) \<in> status_impl_rel\<close>
  unfolding status_impl_rel_def status_rel_def unat_rel_def unat.rel_def
  by (auto simp: in_br_conv)

lemma LEARNED_impl[sepref_import_param]: \<open>(1,LEARNED) \<in> status_impl_rel\<close>
  unfolding status_impl_rel_def status_rel_def unat_rel_def unat.rel_def
  by (auto simp: in_br_conv)

lemma DELETED_impl[sepref_import_param]: \<open>(3,DELETED) \<in> status_impl_rel\<close>
  unfolding status_impl_rel_def status_rel_def unat_rel_def unat.rel_def
  by (auto simp: in_br_conv)


lemma mark_garbageI:
  assumes \<open>mark_garbage_pre (a, b)\<close>
  shows \<open>2 \<le> b\<close> \<open>b-2 < length a\<close>
  using assms STATUS_SHIFT_def
  unfolding mark_garbage_pre_def
  apply (auto simp: arena_is_valid_clause_idx_def arena_lifting)
  by (simp add: less_imp_diff_less valid_arena_def)

sepref_register extra_information_mark_to_delete
sepref_def mark_garbage_impl is \<open>uncurry (RETURN oo extra_information_mark_to_delete)\<close>
  :: \<open>[mark_garbage_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  unfolding extra_information_mark_to_delete_def STATUS_SHIFT_def
  apply (rewrite at \<open>AStatus _ _ \<hole>\<close> annot_snat_unat_downcast[where 'l=32])
  apply (rewrite at \<open>AStatus _ \<hole>\<close> unat_const_fold[where 'a=2])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  supply [simp] = mark_garbageI
  by sepref



lemma bit_shiftr_shiftl_same_le:
  \<open>a << b >> b \<le> a\<close> for a b c :: nat
  unfolding nat_int_comparison
  by (auto simp: nat_shiftr_div nat_shifl_div)

lemma bit_shiftl_shiftr_same_le:
  \<open>a >> b << b \<le> a\<close> for a b c :: nat
  by (auto simp: nat_shiftr_div nat_shifl_div)


lemma valid_arena_arena_lbd_shift_le:
  assumes
    \<open>rdomp (al_assn arena_el_impl_assn) a\<close> and
    \<open>b \<in># dom_m N\<close> and
    \<open>valid_arena a N vdom\<close>
  shows \<open>arena_lbd a b << 5 < max_unat 32\<close>
proof -
  have \<open>2 \<le> b\<close> \<open>b - 2 < length a\<close> and st: \<open>is_Status (a ! (b-2))\<close>
    using assms LBD_SHIFT_def by (auto simp: arena_is_valid_clause_idx_def
      less_imp_diff_less arena_lifting)
  then have H: \<open>rdomp arena_el_impl_assn (a ! (b - 2))\<close>
    using rdomp_al_dest'[of arena_el_impl_assn a] assms
    by auto
  then obtain x :: \<open>32 word\<close> and x51 :: \<open>clause_status\<close> and x52 where
    H: \<open>a ! (b - 2) = AStatus x51 x52 (unat x >> 5)\<close>
      \<open>(unat x AND 3, x51) \<in> status_rel\<close>
    using st bit_shiftr_shiftl_same_le[of \<open>arena_lbd a b\<close> 4]
    by (auto simp: arena_el_impl_rel_def unat_rel_def unat.rel_def
      br_def arena_lbd_def LBD_SHIFT_def)

  show ?thesis
    apply (rule order.strict_trans1[of _ \<open>unat x\<close>])
    using bit_shiftl_shiftr_same_le[of \<open>unat x\<close> 5] unat_lt_max_unat[of \<open>x\<close>] H
    by (auto simp: arena_el_impl_rel_def unat_rel_def unat.rel_def
      br_def arena_lbd_def LBD_SHIFT_def)
qed

lemma arena_mark_used_implI:
  assumes \<open>arena_act_pre a b\<close>
  shows \<open>2 \<le> b\<close> \<open>b - 2 < length a\<close> \<open>is_Status (a ! (b-2))\<close>
    \<open>arena_is_valid_clause_vdom a b\<close>
    \<open>get_clause_LBD_pre a b\<close>
    \<open>rdomp (al_assn arena_el_impl_assn) a \<Longrightarrow> arena_lbd a b << 5 < max_unat 32\<close>
  using assms STATUS_SHIFT_def valid_arena_arena_lbd_shift_le[of a b]
  apply (auto simp: arena_act_pre_def arena_is_valid_clause_idx_def arena_lifting)
  subgoal by (simp add: less_imp_diff_less valid_arena_def)
  subgoal for N vdom by (auto simp: arena_is_valid_clause_vdom_def arena_lifting)
  subgoal for N vdom by (auto simp: arena_is_valid_clause_vdom_def arena_lifting
      get_clause_LBD_pre_def arena_is_valid_clause_idx_def)
  done

lemma mark_used_alt_def:
  \<open>RETURN oo mark_used =
     (\<lambda>arena i. do {
     lbd \<leftarrow> RETURN (arena_lbd arena i); let status = arena_status arena i;
     RETURN (arena[i - STATUS_SHIFT := AStatus status (arena_used arena i OR 1) lbd])})\<close>
  by (auto simp: mark_used_def Let_def intro!: ext)

(* TODO: Wrong name for precondition! *)
sepref_register mark_used mark_used2
sepref_def mark_used_impl is \<open>uncurry (RETURN oo mark_used)\<close>
  :: \<open>[uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  unfolding mark_used_def STATUS_SHIFT_def mark_used_alt_def
  supply [intro] = arena_mark_used_implI
  apply (rewrite at \<open>_ OR \<hole>\<close> unat_const_fold[where 'a=2])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def mark_used2_impl is \<open>uncurry (RETURN oo mark_used2)\<close>
  :: \<open>[uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  unfolding mark_used2_def STATUS_SHIFT_def mark_used_alt_def
  supply [intro] = arena_mark_used_implI
  apply (rewrite at \<open>_ OR \<hole>\<close> unat_const_fold[where 'a=2])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register mark_unused
sepref_def mark_unused_impl is \<open>uncurry (RETURN oo mark_unused)\<close>
  :: \<open>[uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  unfolding mark_unused_def STATUS_SHIFT_def
  supply [intro] = arena_mark_used_implI
  apply (rewrite at \<open>_ - \<hole>\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>_ - \<hole>\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const \<open>TYPE(2)\<close>)
  by sepref

sepref_def mop_arena_mark_used_impl
  is \<open>uncurry mop_arena_mark_used\<close>
  :: \<open>arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a arena_fast_assn\<close>
  unfolding mop_arena_mark_used_def
  by sepref

sepref_def mop_arena_mark_used2_impl
  is \<open>uncurry mop_arena_mark_used2\<close>
  :: \<open>arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a arena_fast_assn\<close>
  unfolding mop_arena_mark_used2_def
  by sepref


paragraph \<open>Marked as used?\<close>

lemma arena_marked_as_used_implI:
  assumes \<open>marked_as_used_pre a b\<close>
  shows \<open>2 \<le> b\<close> \<open>b - 2 < length a\<close> \<open>is_Status (a ! (b-2))\<close>
  using assms STATUS_SHIFT_def
  apply (auto simp: marked_as_used_pre_def arena_is_valid_clause_idx_def arena_lifting)
  subgoal using arena_lifting(2) less_imp_diff_less by blast
  done

sepref_register marked_as_used
sepref_def marked_as_used_impl
  is \<open>uncurry (RETURN oo marked_as_used)\<close>
    :: \<open>[uncurry marked_as_used_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_assn' TYPE(2)\<close>
  supply [intro] = arena_marked_as_used_implI
  unfolding marked_as_used_def STATUS_SHIFT_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register MAX_LENGTH_SHORT_CLAUSE mop_arena_status
sepref_def MAX_LENGTH_SHORT_CLAUSE_impl is \<open>uncurry0 (RETURN MAX_LENGTH_SHORT_CLAUSE)\<close> :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding MAX_LENGTH_SHORT_CLAUSE_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


definition arena_other_watched_as_swap :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
\<open>arena_other_watched_as_swap S L C i = do {
    ASSERT(i < 2 \<and>
      C + i < length S \<and>
      C < length S \<and>
      (C + 1) < length S);
    K \<leftarrow> RETURN (S ! C);
    K' \<leftarrow> RETURN (S ! (1 + C));
    RETURN (L XOR K XOR K')
  }\<close>

lemma arena_other_watched_as_swap_arena_other_watched:
  assumes
    N: \<open>(N, N') \<in> \<langle>arena_el_rel\<rangle>list_rel\<close> and
    L: \<open>(L, L') \<in> nat_lit_rel\<close> and
    C: \<open>(C, C') \<in> nat_rel\<close> and
    i: \<open>(i, i') \<in> nat_rel\<close>
  shows
    \<open>arena_other_watched_as_swap N L C i \<le> \<Down>nat_lit_rel
        (arena_other_watched N' L' C' i')\<close>
proof -
   have eq: \<open>i =i'\<close> \<open>C=C'\<close>
     using assms by auto
   have A: \<open>Pos (L div 2) = A \<Longrightarrow> even L \<Longrightarrow> L = 2 * atm_of A\<close> for A :: \<open>nat literal\<close>
     by (cases A)
      auto
   have Ci: \<open>(C' + i', C' + i') \<in> nat_rel\<close>
     unfolding eq by auto
   have [simp]: \<open>L = N ! (C+i)\<close> if \<open>L' = arena_lit N' (C' + i')\<close> \<open>C' + i' < length N'\<close>
     \<open>arena_lit_pre2 N' C i\<close>
     using that param_nth[OF that(2) Ci N] C i L
     unfolding arena_lit_pre2_def
     apply - apply normalize_goal+
     subgoal for N'' vdom
       using arena_lifting(6)[of N' N'' vdom C i] A[of \<open>arena_lit N' (C' + i')\<close>]
       apply (simp only: list_rel_imp_same_length[of N] eq)
     apply (cases \<open>N' ! (C' + i')\<close>; cases \<open>arena_lit N' (C' + i')\<close>)
     apply (simp_all add: eq nat_lit_rel_def br_def)
     apply (auto split: if_splits simp: eq_commute[of _ \<open>Pos (L div 2)\<close>]
       eq_commute[of _ \<open>ALit (Pos (_ div 2))\<close>] arena_lit_def)
     using div2_even_ext_nat by blast
    done
   have [simp]: \<open>N ! (C' + i') XOR N ! C' XOR N ! Suc C' = N ! (C' + (Suc 0 - i))\<close> if \<open>i < 2\<close>
     using that i
     by (cases i; cases \<open>i-1\<close>)
      (auto simp: bin_pos_same_XOR3_nat)
  have Ci': \<open>(C' + (1 - i'), C' + (1 - i')) \<in> nat_rel\<close>
    unfolding eq by auto
  have [intro!]: \<open>(N ! (Suc C' - i'), arena_lit N' (Suc C' - i')) \<in> nat_lit_rel\<close>
     if \<open>arena_lit_pre2 N' C i\<close> \<open>i < 2\<close>
     using that param_nth[OF _ Ci' N]
     unfolding arena_lit_pre2_def
     apply - apply normalize_goal+
     apply (subgoal_tac \<open>C' + (Suc 0 - i') < length N'\<close>)
     defer
       subgoal for N'' vdom
       using
         arena_lifting(7)[of N' N'' vdom C i]
         arena_lifting(7)[of N' N'' vdom C \<open>Suc 0 - i\<close>]
         arena_lifting(21,4)[of N' N'' vdom C]
        by (cases i')
          (auto simp: arena_lit_pre2_def list_rel_imp_same_length[of N] eq
          simp del: arena_el_rel_def)
     apply (subgoal_tac \<open>(Suc 0 - i') < length (x \<propto> C)\<close>)
     defer
     subgoal for N'' vdom
       using
         arena_lifting(7)[of N' N'' vdom C i]
         arena_lifting(7)[of N' N'' vdom C \<open>Suc 0 - i\<close>]
         arena_lifting(21,4)[of N' N'' vdom C]
        by (cases i')
          (auto simp: arena_lit_pre2_def list_rel_imp_same_length[of N] eq
          simp del: arena_el_rel_def)
     subgoal for N'' vdom
       using
         arena_lifting(6)[of N' N'' vdom C \<open>Suc 0 - i\<close>]
       by (cases \<open>N' ! (C' + (Suc 0 - i'))\<close>)
        (auto simp: arena_lit_pre2_def list_rel_imp_same_length[of N] eq
          arena_lit_def arena_lifting)
     done
   show ?thesis
     using assms
     unfolding arena_other_watched_as_swap_def arena_other_watched_def
       le_ASSERT_iff mop_arena_lit2_def
     apply (refine_vcg)
     apply (auto simp: le_ASSERT_iff list_rel_imp_same_length arena_lit_pre2_def
       arena_lifting
       bin_pos_same_XOR3_nat)
      apply (metis (no_types, lifting) add.comm_neutral add_Suc_right arena_lifting(21,4,7))
      using arena_lifting(4) by auto
qed


sepref_def arena_other_watched_as_swap_impl
  is \<open>uncurry3 arena_other_watched_as_swap\<close>
  :: \<open>(al_assn' (TYPE(64)) uint32_nat_assn)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
       sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply[[goals_limit=1]]
  unfolding arena_other_watched_as_swap_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma arena_other_watched_as_swap_arena_other_watched':
  \<open>(arena_other_watched_as_swap, arena_other_watched) \<in>
     \<langle>arena_el_rel\<rangle>list_rel \<rightarrow> nat_lit_rel \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow>
      \<langle>nat_lit_rel\<rangle>nres_rel\<close>
  apply (intro fun_relI nres_relI)
  using arena_other_watched_as_swap_arena_other_watched
  by blast

lemma arena_fast_al_unat_assn:
  \<open>hr_comp (al_assn unat_assn) (\<langle>arena_el_rel\<rangle>list_rel) = arena_fast_assn\<close>
  unfolding al_assn_def hr_comp_assoc
  by (auto simp: arena_el_impl_rel_def list_rel_compp)

lemmas [sepref_fr_rules] =
  arena_other_watched_as_swap_impl.refine[FCOMP arena_other_watched_as_swap_arena_other_watched',
    unfolded arena_fast_al_unat_assn]


lemma arena_lit_pre2_le_lengthD: \<open>arena_lit_pre2 arena i j \<Longrightarrow> i + j < length arena\<close>
  apply (auto simp: arena_lit_pre2_def)
  using arena_lifting(7) nat_le_iff_add by auto

sepref_def mop_arena_update_lit_code
  is \<open>uncurry3 mop_arena_update_lit\<close>
  :: \<open>[\<lambda>(((_, _), _), N). length N \<le> sint64_max]\<^sub>a
  sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow> arena_fast_assn\<close>
  supply [intro] = arena_lit_implI
  supply [dest] = arena_lit_pre2_le_lengthD
  unfolding mop_arena_update_lit_def arenap_update_lit_def
  by sepref

lemma arena_shorten_preI:
  assumes \<open>arena_shorten_pre C j arena\<close>
  shows
    \<open>j \<ge> 2\<close> and
    \<open>C - Suc 0  < length arena\<close> and
    \<open>C \<ge> Suc 0\<close> and
    \<open>j > MAX_LENGTH_SHORT_CLAUSE \<Longrightarrow> C \<ge> 3\<close>
  using assms arena_lifting[of arena _ _ C]
  unfolding arena_shorten_pre_def by (auto simp: arena_is_valid_clause_idx_def SHIFTS_def
      header_size_def
    intro: less_imp_diff_less)

sepref_def mop_arena_shorten_code
  is \<open>uncurry2 mop_arena_shorten\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow>\<^sub>a arena_fast_assn\<close>
  supply [dest] = arena_shorten_preI
  supply [dest] = arena_lit_pre2_le_lengthD
  unfolding mop_arena_shorten_def arena_shorten_def SIZE_SHIFT_def POS_SHIFT_def
  apply (rewrite at  \<open>_[_ := ASize (_ - \<hole>), _ := _]\<close> unat_const_fold[where 'a=32])
  apply (rewrite at \<open>_[_ := ASize (_ - \<hole>)]\<close> unat_const_fold[where 'a=32])
  apply (rewrite at \<open>_[_ := _, _ := APos \<hole>]\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE (64)\<close>)
    apply (rewrite  at \<open>( _ < \<hole>)\<close> annot_unat_snat_upcast[where 'l=64])
  by sepref

end

sepref_def mop_arena_length_impl
  is \<open>uncurry mop_arena_length\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding mop_arena_length_def
  by sepref

sepref_def mop_arena_status_impl
  is \<open>uncurry mop_arena_status\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a status_impl_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_arena_status_def
  by sepref



sepref_def status_neq_impl is [] \<open>uncurry (RETURN oo (\<noteq>))\<close>
  :: \<open>(unat_assn' TYPE(32))\<^sup>k *\<^sub>a (unat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

lemmas [sepref_fr_rules] = status_neq_impl.refine[FCOMP status_neq_refine1]

experiment begin
export_llvm
  arena_length_impl
  arena_lit_impl
  arena_status_impl
  swap_lits_impl
  arena_lbd_impl
  arena_pos_impl
  update_lbd_impl
  update_pos_impl
  mark_garbage_impl
  mark_used_impl
  mark_unused_impl
  marked_as_used_impl
  MAX_LENGTH_SHORT_CLAUSE_impl
  mop_arena_status_impl
end

end
