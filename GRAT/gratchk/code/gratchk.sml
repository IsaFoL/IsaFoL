fun println x = print (x ^ "\n")

val int_of_gi = IntInf.toInt o Grat_Check.integer_of_int
val gi_of_int = Grat_Check.Int_of_integer o IntInf.fromInt
val int_of_gn = IntInf.toInt o Grat_Check.integer_of_nat
val gn_of_int = Grat_Check.nat_of_integer o IntInf.fromInt

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
  
fun verify_unsat a frml_end it = let
  val _ = print ("Verifying unsat\n");
  val vresult = Grat_Check.verify_unsat_impl_wrapper a frml_end it ()
  val _ = print ("Done\n");
in
  (case vresult of
    Grat_Check.Inl e => print ("ERROR: " ^ etostr e)
  | Grat_Check.Inr _ => print ("s VERIFIED UNSAT"));
  
  print "\n"
end
  
fun verify_sat a frml_end = let
  val _ = print ("Verifying sat\n");
  val vresult = Grat_Check.verify_sat_impl_wrapper a frml_end ()
  val _ = print ("Done\n");
in
  (case vresult of
    Grat_Check.Inl e => print ("ERROR: " ^ etostr e)
  | Grat_Check.Inr _ => print ("s VERIFIED SAT"));
  
  print "\n"
end

fun dump a pos = let
  fun d i =
    if i<Array.length a andalso i<pos+100 then let
        val x = int_of_gi(Array.sub(a,i));
        val _ = print(Int.toString(x));
        val _ = if x<>0 then print " " else print "\n";
      in d (i+1) end
    else
      ()
in
 d pos;
 print "\n"
end

datatype checker_mode = MODE_SAT | MODE_UNSAT | MODE_DUMP of int

fun checker mode cnf_name grat_name = let
  val a = Array.array (1024,gi_of_int 0);
  
  val cnf_start = 1;
  val _ = print ("Reading cnf\n");
  val (proof_start,a) = Dimacs_Parser.parse_dimacs_file_map_to_dynarray cnf_name gi_of_int (cnf_start,a);
  val _ = print ("Reading proof\n");
  val (proof_end,a) = Dimacs_Parser.parse_dimacs_file_map_to_dynarray grat_name gi_of_int (proof_start,a);
  val _ = print ("Done\n");
  val _ = print ("Read " ^ Int.toString (proof_end-1) ^ " ints\n")
  val _ = print ("Buffer " ^ Int.toString (Array.length a) ^ " ints\n")
  val _ = print ("Last read: " ^ Int.toString (int_of_gi (Array.sub (a,proof_end - 1))) ^ "\n");
  
in
  case mode of
    MODE_SAT => let
        val frml_end = gn_of_int proof_start
        val _ = Dimacs_Parser.dyn_array_set a proof_end (gi_of_int 0)
      in
        verify_sat a frml_end
      end
  | MODE_UNSAT => let
        val it = gn_of_int proof_end
        val frml_end = gn_of_int proof_start
      in
        verify_unsat a frml_end it      
      end
  | MODE_DUMP pos => dump a pos
  
end

fun print_help () = (
  println("Usage: " ^ CommandLine.name() ^ " <mode> cnf-file cert-file");
  println("  where mode is 'sat' or 'unsat'")
)

fun process_args ["sat",cnf_name,grat_name] = checker MODE_SAT cnf_name grat_name
  | process_args ["unsat",cnf_name,grat_name] = checker MODE_UNSAT cnf_name grat_name
  | process_args ["dump",cnf_name,grat_name,ofs] 
      = checker (MODE_DUMP (valOf (Int.fromString ofs))) cnf_name grat_name
  | process_args _ = (
      println("ERROR: Invalid command line arguments");
      print_help()
    )    

fun main () = let
  val args = CommandLine.arguments ();
in
  process_args args
end


val _ = if MLton.isMLton then main() else ()
