(*use "full_SAT_Cached.sml";
use "dimacs_parser.sml";*)

fun println x = print (x ^ "\n")

val int_of_gi = IntInf.toInt o SAT_Solver.integer_of_int
val gi_of_int = SAT_Solver.Int_of_integer o IntInf.fromInt
val int_of_gn = IntInf.toInt o SAT_Solver.integer_of_nat
val gn_of_int = SAT_Solver.uint32_of_nat o SAT_Solver.nat_of_integer o IntInf.fromInt

exception LitTooLarge of Int.int

fun lit_of_nat n =
  if Word.toLargeInt n mod 2 = 0 then 1+(Word.toLargeInt n div 2)
  else ~(1+((Word.toLargeInt n) div 2))

fun print_model (xs, i) =
    let
      fun map_from j =
          if j >= int_of_gn i then ()
          else
            ((print o (fn n => IntInf.toString n ^ " ") o lit_of_nat)
                (Array.sub (xs, j));
                 map_from (j+1))
    in (print "v "; map_from 0; print "\n") end

fun nat_of_lit n =
  let val m = if n < 0 then (2*(~n-1)+1) else (2*(n-1))
  in
    if IntInf.fromInt m >= 2147483648 (* = 2^31*)
    then (print (IntInf.toString (IntInf.fromInt m)); raise (LitTooLarge m))
    else gn_of_int m
  end

fun natotostr NONE = ""
  | natotostr (SOME n) = " (pos = "^Int.toString (int_of_gn n)^")"

fun intotostr NONE = ""
  | intotostr (SOME i) = " (val = "^Int.toString (int_of_gi i)^")"

fun etostr (msg,(vo,po)) = msg ^ intotostr vo ^ natotostr po

fun print_clause_at a i =
  let
    val l = int_of_gi (Array.sub (a,i))
    val _ = print (Int.toString l)
  in
    if l = 0 then
      print "\n"
    else (print " "; print_clause_at a (i+1))
  end

fun print_seq_at a i 0 = (print "<...>\n")
  | print_seq_at a i n =
    if i < Array.length a then
      let
        val x = int_of_gi (Array.sub (a,i))
        val _ = print (Int.toString x)
        val _ = print (if x=0 then "\n" else " ")
      in
        print_seq_at a (i+1) (n-1)
      end
    else print "<EOF>\n"

fun print_clause_at [] = print "\n"
  | print_clause_at  (a :: xs) =
    let
      val l = (lit_of_nat a)
      val _ = print (IntInf.toString l)
    in (print " "; print_clause_at xs)
    end

fun print_clauses id [] = ()
  | print_clauses id (i::xs) = (
      print (Int.toString id ^ ": ");
      print_clause_at i;
      print_clauses (id + 1) xs
    )

fun print_stat (propa, (confl, (dec, (res, (lres, (ures, (gcs, _))))))) end_of_init end_of_processing =
  let
    fun print_timer d t = print ("c " ^ d ^ ": " ^ Time.toString (#usr (#nongc t)) ^ " s (usr) " ^  Time.toString (#sys (#nongc t)) ^ " s (sys)\n");
    fun print_timer_GC d t = print ("c " ^ d ^ ": " ^ Time.toString (#usr (#gc t)) ^ " s (usr) " ^  Time.toString (#sys (#gc t)) ^ " s (sys)\n");
    val clock = Time.toSeconds (#usr (#nongc end_of_processing)) + Time.toSeconds (#sys (#nongc end_of_processing));
    fun print_stat d t =
        (print ("c " ^ d ^ ": " ^ IntInf.toString (Uint64.toInt t) ^ "\n");
         if clock <> 0 then print ("c " ^ d ^ " per s: " ^ IntInf.toString (Uint64.toInt t div clock) ^ "\n") else ())
     val _ = print "c\nc\nc ***** stats *****\n"
     val _ = print_timer "time init" end_of_init
     val _ = print_timer "time solving" end_of_processing
     val _ = print_timer_GC "time GC" end_of_processing
     val _ = print_stat "propagations" propa
     val _ = print_stat "conflicts" confl
     val _ = print_stat "decisions" dec
     val _ = print_stat "reductions" res
     val _ = print_stat "local restarts" lres
     val _ = print_stat "GCs" gcs
     val _ = print_stat "local literals set at level 0" ures
  in
   ()
  end
fun solver print_modelb print_stats norestart noreduction nounbounded cnf_name = let
  val timer = Timer.totalCPUTimer ()
  val problem = Dimacs_Parser.parse_dimacs_file_map_to_list cnf_name nat_of_lit;
  val end_of_init = Timer.checkCPUTimes timer
  val timer = Timer.totalCPUTimer ()
  val (SAT, stat) = SAT_Solver.isaSAT_code (not norestart, (not noreduction, nounbounded)) problem ();
  val end_of_processing = Timer.checkCPUTimes timer
  val _ = (if print_stats then print_stat stat end_of_init end_of_processing else ());
  val _ =
        (case SAT of
             NONE => print "s UNSATISFIABLE\n"
           | SOME SAT => (if print_modelb then ignore (print_model SAT) else (); print "s SATISFIABLE\n"))
  in
    ()
  end

fun print_help () = (
  println("Usage: [--verbose] [--stat]" ^ CommandLine.name() ^ " cnf-file");
  println("  where <cnf-file> is a non-compressed file in dimacs format");
  println("  The result (SAT or UNSAT) is printed");
  println("  Use option --stat to print the number of propagations,");
  println("   conflicts, and decisions. ");
  println("  Use option --model to print a model if one exists.");
  println("  Use option --norestart to d%eactivate restarts.");
  println("  Use option --noreduction to deactivate DB reduction.");
  println("  Use option --nobounded to force the usage of IntInf.");
  println("  Use option --version to print the git id of IsaFoL when generating code.")
)

fun contains x xs =
  case List.find (fn y => y = x) xs of
      NONE => false
    | SOME _ => true

fun process_args [] = print_help() 
  | process_args args =
    if (contains "--version" args) then println("c version: " ^ SAT_Solver.version ^"\n")
    else
      solver (contains "--model" args)
             (contains "--stat" args)
             (contains "--norestart" args)
             (contains "--noreduction" args)
             (contains "--nobounded" args)
             (List.last args)


fun main () = let
  val args = CommandLine.arguments ();
in
  process_args args
end


val _ = if MLton.isMLton then main() else ()
