(*use "full_SAT_Cached.sml";
use "dimacs_parser.sml";*)

fun println x = print (x ^ "\n")

val int_of_gi = IntInf.toInt o SAT_Solver.integer_of_int
val gi_of_int = SAT_Solver.Int_of_integer o IntInf.fromInt
val int_of_gn = IntInf.toInt o SAT_Solver.integer_of_nat
val gn_of_int = SAT_Solver.uint32_of_nat o SAT_Solver.nat_of_integer o IntInf.fromInt

fun nat_of_lit n =
  let val m = if n < 0 then (2*(~n-1)+1) else (2*(n-1))
  in
    gn_of_int m
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


fun print_clauses id [] = ()
  | print_clauses id (i::xs) = (
      print (Int.toString id ^ ": ");
      List.map (fn L => (print ((Int.toString o int_of_gn) L); print " ")) i;
      print "\n";
      print_clauses (id+1) xs
    )

fun checker cnf_name = let
  fun output status = print (cnf_name ^ ": " ^ status ^ "\n")
  val problem = Dimacs_Parser.parse_dimacs_file_map_to_list cnf_name nat_of_lit;
  val _ = output "end of parsing"

  val SAT = SAT_Solver.sAT_wl_code problem ();
  val _ = if SAT then output "SAT" else output "UNSAT"
  in
    ()
  end

fun process_args [cnf_name] = checker cnf_name

fun main () = let
  val args = CommandLine.arguments ();
in
  process_args args
end


val _ = if MLton.isMLton then main() else ()
