(* Author: Mathias Fleury, MPII


Simprocs for multisets, based on Larry Paulson's simprocs for
natural numbers and numerals.
*)

signature COMM_MONOID_ADD_SIMPROCS =
sig
  val eq_cancel: Proof.context -> cterm -> thm option
  val less_cancel: Proof.context -> cterm -> thm option
  val less_eq_cancel: Proof.context -> cterm -> thm option
  val diff_cancel: Proof.context -> cterm -> thm option
end;

structure Comm_Monoid_add_Simprocs : COMM_MONOID_ADD_SIMPROCS =
struct

structure EqCancelComm_Monoid_add = CancelNumeralsFun
 (open Comm_Monoid_add_Cancel_Common
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin @{const_name HOL.eq} dummyT
  val bal_add1 = @{thm iterate_add_eq_add_iff1} RS trans
  val bal_add2 = @{thm iterate_add_eq_add_iff2} RS trans
);

structure EqCancelComm_Monoid_less = CancelNumeralsFun
 (open Multiset_Cancel_Common
  val mk_bal   = HOLogic.mk_binrel @{const_name Orderings.less}
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less} dummyT
  val bal_add1 = @{thm iterate_add_less_iff1} RS trans
  val bal_add2 = @{thm iterate_add_less_iff2} RS trans
);

structure EqCancelComm_Monoid_less_eq = CancelNumeralsFun
 (open Multiset_Cancel_Common
  val mk_bal   = HOLogic.mk_binrel @{const_name Orderings.less_eq}
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less_eq} dummyT
  val bal_add1 = @{thm iterate_add_less_eq_iff1} RS trans
  val bal_add2 = @{thm iterate_add_less_eq_iff2} RS trans
);

structure DiffCancelComm_Monoid_less_eq = CancelNumeralsFun
 (open Multiset_Cancel_Common
  val mk_bal   = HOLogic.mk_binop @{const_name Groups.minus}
  val dest_bal = HOLogic.dest_bin @{const_name Groups.minus} dummyT
  val bal_add1 = @{thm mset_diff_add_eq1} RS trans
  val bal_add2 = @{thm mset_diff_add_eq2} RS trans
);

val eq_cancel = EqCancelComm_Monoid_add.proc;
val less_cancel = EqCancelComm_Monoid_less.proc;
val less_eq_cancel = EqCancelComm_Monoid_less_eq.proc;
val diff_cancel = DiffCancelComm_Monoid_less_eq.proc;

end
