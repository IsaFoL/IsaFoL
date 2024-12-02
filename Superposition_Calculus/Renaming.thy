theory Renaming
  imports 
    Fun_Extra 
    Nonground_Clause
begin

(* TODO Martin: Where should we put this?  *)
section \<open>Renamings as Bijections on Natural Numbers\<close>

text \<open>Renamings can be defined as bijections between variables; They then become invertible (both
from the left and from the right). The question is whether such bijections can be efficiently
computed for variable types used in practice. Here, we show that it is indeed possible to
efficiently compute such a bijection for the type of natural numbers.\<close>

lemma renaming_nats_spec:
  fixes k m :: nat and rename :: "nat \<Rightarrow> nat"
  defines "rename n \<equiv> if n < k then (Suc m + n) mod k else n"
  assumes "Suc (m + m) < k"
  shows "bij rename" and "\<And>x. x \<le> m \<Longrightarrow> m < rename x"
proof (intro bijI)
  fix x assume "x \<le> m"
  with \<open>Suc (m + m) < k\<close> have "Suc m + x < k"
    by presburger
  thus "m < rename x"
    unfolding rename_def
    by (simp flip: add_Suc)
next
  have "m < k"
    using \<open>Suc (m + m) < k\<close> by presburger

  show "inj rename"
  proof (rule injI)
    fix x y assume hyp: "rename x = rename y"
    hence "x < k \<longleftrightarrow> y < k"
      unfolding rename_def
      by (metis less_imp_add_positive mod_less_divisor trans_less_add2)
    show "x = y"
    proof (cases "x < k \<and> y < k")
      case True
      then show ?thesis
        using hyp
        unfolding rename_def
        apply simp
        using \<open>m < k\<close>
        by (metis (no_types, lifting) add_diff_cancel_left linear mod_eq_dvd_iff_nat mod_nat_eqI
            nat_add_left_cancel_le plus_1_eq_Suc)
    next
      case False
      then show ?thesis
        using hyp unfolding rename_def
        using \<open>x < k \<longleftrightarrow> y < k\<close>
        by simp
    qed
  qed

  define f :: "nat \<Rightarrow> nat" where
    "\<And>n. f n = (if n < k then (k + n - Suc m) mod k else n)"

  have f_mono_wrt_Suc_k: "f x < k" if "x < k" for x
    using that unfolding f_def by simp
  show "surj rename"
  proof (rule surjI)
    fix x
    show "rename (f x) = x"
    proof (cases "x < k")
      case True
      then show ?thesis
        apply (simp add: rename_def f_mono_wrt_Suc_k)
        unfolding f_def
        using \<open>m < k\<close>
        by (simp add: mod_add_right_eq flip: add_Suc)
    next
      case False
      thus ?thesis
        by (simp add: rename_def f_def)
    qed
  qed
qed

text \<open>In practice, an implementation will probably restrict variables to 8-bit, 16-bit, 32-bits, or
64-bit unsigned integer. In that case, the parameter \<^term>\<open>k\<close> can simply be set to the maximum of
the used type, e.g., \<^term>\<open>2^16 - 1 :: nat\<close>. The if-then-else comparison then becomes trivially true
and need not be performed. Likewise, the modulo operation is corresponds to the default wrap-around
behaviour of integer arithmetic commonly implemented by prosessors. The complete renaming function
then simplifies to \<^term>\<open>Suc m + n\<close>.\<close>

definition renamings_apart_nat ::
  "nat multiset \<Rightarrow> nat multiset \<Rightarrow> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat)" where
  "renamings_apart_nat X Y \<equiv>
    let
      max\<^sub>X = if X = {#} then 0 else Max_mset X;
      max\<^sub>Y = if Y = {#} then 0 else Max_mset Y;
      m = max max\<^sub>X max\<^sub>Y;
      k = 2 * m + 2;
      \<rho>\<^sub>X = \<lambda>x. if x < k then (Suc m + x) mod k else x;
      \<rho>\<^sub>Y = \<lambda>x. x
    in (\<rho>\<^sub>X, \<rho>\<^sub>Y)"

text \<open>The parameters are multisets because one could count the number of variables and swap the
bijections such that the smaller multiset (i.e. clause) gets renamed. Depending on the
implementation, this could save some some memory allocation.\<close>

text \<open>The following lemma shows that \<^const>\<open>renamings_apart_nat\<close> fulfills the renaming requirements
found in the inference rules of the first-order superposition calculus.\<close>

lemma
  assumes "renamings_apart_nat X Y = (\<rho>\<^sub>X, \<rho>\<^sub>Y)"
  shows "bij \<rho>\<^sub>X" and "bij \<rho>\<^sub>Y" and "(\<rho>\<^sub>X ` set_mset X) \<inter> (\<rho>\<^sub>Y ` set_mset Y) = {}"
proof -
  define max\<^sub>X where
    "max\<^sub>X \<equiv> if X = {#} then 0 else Max_mset X"

  define max\<^sub>Y where
    "max\<^sub>Y \<equiv> if Y = {#} then 0 else Max_mset Y"

  define m where
    "m = max max\<^sub>X max\<^sub>Y"

  define k where
    "k = 2 * m + 2"

  have "Suc (m + m) < k"
    unfolding m_def k_def by presburger

  have \<rho>\<^sub>X_def: "\<rho>\<^sub>X = (\<lambda>x. if x < k then (Suc m + x) mod k else x)" and \<rho>\<^sub>Y_def: "\<rho>\<^sub>Y = (\<lambda>x. x)"
    using assms unfolding renamings_apart_nat_def Let_def
    unfolding max\<^sub>X_def[symmetric] max\<^sub>Y_def[symmetric] m_def[symmetric] k_def[symmetric]
    by simp_all

  have 2: "\<rho>\<^sub>Y ` set_mset Y = set_mset Y"
    by (metis (no_types, lifting) assms multiset.map_ident_strong multiset.set_map prod.inject
        renamings_apart_nat_def)

  have "\<forall>x \<in># X. x \<le> max\<^sub>X"
    by (simp add: max\<^sub>X_def)
  hence "\<forall>x \<in># X. x \<le> m"
    by (auto simp: m_def)
  hence "\<forall>x \<in># X. m < \<rho>\<^sub>X x"
    using renaming_nats_spec[of m k, OF \<open>Suc (m + m) < k\<close>]
    unfolding \<rho>\<^sub>X_def
    by (simp add: m_def)

  moreover have "\<forall>y \<in># Y. y \<le> max\<^sub>Y"
    by (simp add: max\<^sub>Y_def)

  ultimately show "(\<rho>\<^sub>X ` set_mset X) \<inter> (\<rho>\<^sub>Y ` set_mset Y) = {}"
    unfolding 2 m_def
    by fastforce

  show "bij \<rho>\<^sub>X"
    using renaming_nats_spec(1)[of m k, OF \<open>Suc (m + m) < k\<close>, folded \<rho>\<^sub>X_def] .

  show "bij \<rho>\<^sub>Y"
    by (simp add: \<rho>\<^sub>Y_def bij_betw_def)
qed

end
