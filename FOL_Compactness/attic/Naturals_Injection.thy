(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2024 *)

theory Naturals_Injection
imports
  Main
begin

definition numpair :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  \<open>numpair x y = (2^x) * (2 * y + 1)\<close>

lemma numpair_inj_x: \<open>numpair x1 y1 = numpair x2 y2 \<Longrightarrow> x1 = x2\<close>
  unfolding numpair_def 
proof (induction x1 arbitrary: x2)
  case 0
  then show ?case
    by (metis Groups.mult_ac(2) bot_nat_0.not_eq_extremum dvd_triv_left even_Suc even_add 
        even_mult_exp_div_exp_iff nonzero_mult_div_cancel_left plus_1_eq_Suc power_eq_0_iff)
next
  case (Suc x1)
  then have "x2 > 0"
    by (metis even_mult_iff even_numeral even_plus_one_iff even_power less_Suc_eq_0_disj)
  then obtain px2 where px2_is: "x2 = Suc px2"
    using not0_implies_Suc by blast
  then have \<open>2 ^ Suc x1 * (2 * y1 + 1) = 2 ^ Suc px2 * (2 * y2 + 1)\<close>
    using Suc(2) by simp
  then have \<open>2 ^ x1 * (2 * y1 + 1) = 2 ^ px2 * (2 * y2 + 1)\<close>
    by simp
  then show ?case
    using Suc(1) px2_is by blast
qed

lemma numpair_inj: \<open>numpair x1 y1 = numpair x2 y2 \<Longrightarrow> x1 = x2 \<and> y1 = y2\<close>
  using numpair_inj_x
  by (metis Suc_eq_plus1 bot_nat_0.extremum_strict less_exp mult_cancel1 nat.simps(1) nat.simps(3)
      numerals(2) numpair_def)

(* INJ_INVERSE2 in hol-light *)
lemma inj_inverse2: \<open>(\<forall>x1 y1 x2 y2. P x1 y1 = P x2 y2 \<longleftrightarrow> (x1 = x2) \<and> (y1 = y2)) \<Longrightarrow>
   \<exists>F S. \<forall>x y. (F (P x y) = x) \<and> (S (P x y) = y)\<close>
proof -
  assume inj: \<open>\<forall>x1 y1 x2 y2. P x1 y1 = P x2 y2 \<longleftrightarrow> (x1 = x2) \<and> (y1 = y2)\<close>
  obtain F where F_is: \<open>F = (\<lambda>z. (SOME x. \<exists>y. P x y = z))\<close> by simp
  obtain S where S_is: \<open>S = (\<lambda>z. (SOME y. \<exists>x. P x y = z))\<close> by simp
  show \<open>\<exists>F S. \<forall>x y. F (P x y) = x \<and> S (P x y) = y\<close> using F_is S_is
    by (metis (mono_tags, lifting) inj)
qed
 
consts numfst :: "nat \<Rightarrow> nat" numsnd :: "nat \<Rightarrow> nat"
specification (numfst) \<open>\<forall>x y. numfst (numpair x y) = x\<close>
  using inj_inverse2 numpair_inj by metis

specification (numsnd) \<open>\<forall>x y. numsnd (numpair x y) = y\<close>
  using inj_inverse2 numpair_inj by metis

lemma numfst_simp [simp]: \<open>numfst (numpair x y) = x\<close>
  using HOL.nitpick_choice_spec(1) by simp

lemma numsnd_simp [simp]: \<open>numsnd (numpair x y) = y\<close>
  using HOL.nitpick_choice_spec(2) by simp    

end