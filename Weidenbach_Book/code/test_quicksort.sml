(*
 * Run some tests on the quicksort implementation
 * (For debugging)
 *)

use "quicksort.sml";

structure Isa = struct
  type nat = IsaQuicksort.nat

  (* We don't want to test with IntInf *)
  val nat_of_integer = IsaQuicksort.nat_of_integer o IntInf.fromInt
  val integer_of_nat = IntInf.toInt o IsaQuicksort.integer_of_nat

  fun nats_of_ints (xs : int list) : nat Array.array =
    Array.fromList (map nat_of_integer xs)
  fun ints_of_nats (xs : nat Array.array) : int list =
    map integer_of_nat (Array.toList xs)


  fun array_length (xs : 'a Array.array) : nat = nat_of_integer (Array.length xs)
  fun list_length (xs : 'a list) : nat = nat_of_integer (List.length xs)

  fun array_last_index (xs : 'a Array.array) =
    nat_of_integer (integer_of_nat (array_length xs) - 1)
  fun list_last_index (xs : 'a list) =
    nat_of_integer (integer_of_nat (list_length xs) - 1)

  fun qsort (xs : nat Array.array) : nat Array.array =
    #1(IsaQuicksort.full_quicksort_code (xs, array_length xs) ())
  fun qsort' xs = ints_of_nats (qsort (nats_of_ints xs))

  fun partition (i : nat) (j : nat) (xs : nat Array.array) : nat Array.array * nat =
    case IsaQuicksort.partition_between_code i j (xs, array_length xs) () of
      ((xs', _), p) => (xs', p)
  fun partition' i j xs =
    case partition (nat_of_integer i) (nat_of_integer j) (nats_of_ints xs) of
      (xs', p) => (ints_of_nats xs', integer_of_nat p)
end

type nat = Isa.nat

exception Assert
fun assert b = if b then () else raise Assert

exception WrongSortingResult of int list


val lt = op<
val gt = op>


(* Compute sortings using our function and using SML/NJ's function *)
fun computeSorting (xs : int list) : nat Array.array * nat Array.array =
  let val inputArray    = Isa.nats_of_ints xs
      val expectedList  = ListMergeSort.sort gt xs
      val expectedArray = Array.fromList (map Isa.nat_of_integer expectedList)
      val actualArray   = Isa.qsort inputArray
  in
    (actualArray, expectedArray)
  end


(* Compare the results and raise WrongSortingResult if they don't match *)
fun runSortingTest (xs : int list) : unit =
  case computeSorting xs of
    (array1, array2) =>
    if Array.toList array1 = Array.toList array2 then ()
    else raise (WrongSortingResult xs)


(* Same function as in Isabelle *)
fun sublist (xs : 'a list) (i : int) (j : int) = List.take (List.drop (xs, i), 1+j-i)

(* Check some properties of the partition function *)
fun checkPartition (i : int) (j : int) (xs : int list) : bool =
  let val (ys, p)         = Isa.partition' i j xs
      val ()              = assert (i <= p andalso p <= j)
      val px              = List.nth(ys, p)
      val (less, greater) = (sublist ys i (p-1), sublist ys (p+1) j)
  in
    List.all (fn x => not (x > px)) less andalso
    List.all (fn x => not (x < px)) greater
  end

(* Run the test for the partition function for some given list and indices *)
fun runPartitionTest (i : int) (j : int) (xs : int list) =
  if checkPartition i j xs then ()
  else raise WrongSortingResult xs

(* Compute all pairs (i,j) with i<=j<l *)
fun intervals (l : int) : (int*int) list =
  List.concat (List.tabulate (l, fn i => List.tabulate (l-i, fn j => (i,i+j))))

(* Run the partition test with all pairs (i,j) *)
fun runPartitionTests (xs : int list) : unit =
  List.app (fn (i, j) => runPartitionTest i j xs) (intervals (length xs))
    handle Assert => (raise WrongSortingResult xs)


(* Run partition and sorting tests on a list *)
fun runSingleTest (xs : int list) : unit =
  let in
    runPartitionTests xs;
    runSortingTest xs
  end


(* interleave :: 'a => 'a list => 'a list list *)
fun interleave x      [] = [[x]]
  | interleave x (y::ys) =
      (x :: y :: ys) ::
      (map (fn zs => y :: zs) (interleave x ys))


(* permutations :: 'a list => 'a list list *)
fun permutations       nil = [[]]
  | permutations (x :: xs) =
      List.concat (map (fn zs => (interleave x zs)) (permutations xs))


(* Runs all tests on all permutations of a list *)
val runPermutationTest = List.app runSingleTest o permutations


(* Run all permutation tests on some lists. If there was an error with some
 * list, output it *)
fun runAllTests () : int list option =
  let
    val () = runSingleTest []
    val () = runSingleTest [1]
    val () = runSingleTest [42]
    val () = runSingleTest [~42, 42]
    val () = runPermutationTest [1,2]
    val () = runPermutationTest [1,2,3]
    val () = runPermutationTest [4,8,15,16,23,42]
  in
    NONE (* Everything fine! *)
  end
    handle WrongSortingResult xs => SOME xs

(* Main: Execute tests and check that there was no error *)
val None = runAllTests ();
