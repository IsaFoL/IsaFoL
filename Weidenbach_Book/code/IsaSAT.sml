(*use "full_SAT_Cached.sml";
use "dimacs_parser.sml";*)

fun println x = print (x ^ "\n")

val int_of_gi = IntInf.toInt o SAT_Solver.integer_of_int
val gi_of_int = SAT_Solver.Int_of_integer o IntInf.fromInt
val int_of_gn = IntInf.toInt o SAT_Solver.integer_of_nat
val gn_of_int = SAT_Solver.uint32_of_nat o SAT_Solver.nat_of_integer o IntInf.fromInt

exception LitTooLarge of Int.int

fun lit_of_nat n =
  if Word.toLargeInt n mod 2 = 0 then Word.toLargeInt n div 2
  else ~(Word.toLargeInt n div 2)

val print_model = map (print o (fn n => IntInf.toString n ^ " ") o lit_of_nat)

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


fun print_clauses id a [] = ()
  | print_clauses id a (i::xs) = (
      print (Int.toString id ^ ": ");
      print_clause_at a (int_of_gn i);
      print_clauses (id+1) a xs
    )

fun checker print_modelb cnf_name = let
  val problem = Dimacs_Parser.parse_dimacs_file_map_to_list cnf_name nat_of_lit;
  val SAT = SAT_Solver.isaSAT_code problem ();
  val _ =
        (case SAT of
             NONE => print "UNSAT"
           | SOME SAT => if print_modelb then ignore (print_model SAT) else print "SAT")
  in
    ()
  end

fun print_help () = (
  println("Usage: [--verbose] " ^ CommandLine.name() ^ " cnf-file");
  println("  where <cnf-file> is a non-compressed file in dimacs format");
  println("  The result (SAT or UNSAT) is printed");
  println("  Use option --verbose to print the model if one exists")
)

fun process_args [cnf_name] = checker false cnf_name
  | process_args ["--verbose", cnf_name] = checker true cnf_name
  | process_args _ = print_help() 

fun main () = let
  val args = CommandLine.arguments ();
in
  process_args args
end


val _ = if MLton.isMLton then main() else ()
