theory PAC_More_Poly
  imports "HOL-Library.Poly_Mapping" "HOL-Algebra.Polynomials" "Polynomials.MPoly_Type_Class"
  "HOL-Algebra.Module"
  "HOL-Library.Countable_Set"
  "Polynomials.MPoly_PM"
begin


lemma Const\<^sub>0_add:
  \<open>Const\<^sub>0 (a + b) = Const\<^sub>0 a + Const\<^sub>0 b\<close>
  by transfer
   (simp add: Const\<^sub>0_def single_add)

lemma Const_mult:
  \<open>Const (a * b) = Const a * Const b\<close>
  by transfer
     (simp add: Const\<^sub>0_def times_monomial_monomial)

lemma Const\<^sub>0_mult:
  \<open>Const\<^sub>0 (a * b) = Const\<^sub>0 a * Const\<^sub>0 b\<close>
  by transfer
     (simp add: Const\<^sub>0_def times_monomial_monomial)

lemma Const0[simp]:
  \<open>Const 0 = 0\<close>
  by transfer (simp add: Const\<^sub>0_def)

lemma (in -) Const_uminus[simp]:
  \<open>Const (-n) = - Const n\<close>
  by transfer
    (auto simp: Const\<^sub>0_def monomial_uminus)

lemma [simp]: \<open>Const\<^sub>0 0 = 0\<close>
  \<open>MPoly 0 = 0\<close>
  supply [[show_sorts]]
  by (auto simp: Const\<^sub>0_def zero_mpoly_def)

lemma Const_add:
  \<open>Const (a + b) = Const a + Const b\<close>
  by transfer
   (simp add: Const\<^sub>0_def single_add)

instance mpoly :: (comm_semiring_1) comm_semiring_1
  by standard

end