(* Author: Mathias Fleury, MPII


Simprocs for multisets, based on Larry Paulson's simprocs for
natural numbers and numerals.
*)

signature MULTISET_SIMPROCS =
sig
  val eq_cancel_msets: Proof.context -> cterm -> thm option
end;

structure Comm_Monoid_add_Simprocs : MULTISET_SIMPROCS =
struct

structure EqCancelComm_Monoid_add = CancelNumeralsFun
 (open Comm_Monoid_add_Cancel_Common
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin @{const_name HOL.eq} dummyT
  val bal_add1 = @{thm iterate_add_eq_add_iff1} RS trans
  val bal_add2 = @{thm iterate_add_eq_add_iff2} RS trans
);

val eq_cancel_msets = EqCancelComm_Monoid_add.proc;


end
