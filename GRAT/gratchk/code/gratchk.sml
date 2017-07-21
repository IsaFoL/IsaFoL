fun println x = print (x ^ "\n")

val int_of_gi = IntInf.toInt o Grat_Check.integer_of_int
val gi_of_int = Grat_Check.Int_of_integer o IntInf.fromInt
val int_of_gn = IntInf.toInt o Grat_Check.integer_of_nat
val gn_of_int = Grat_Check.nat_of_integer o IntInf.fromInt

fun natotostr NONE = ""
  | natotostr (SOME n) = " (pos = "^Int.toString (int_of_gn n)^")"

fun intotostr NONE = ""
  | intotostr (SOME i) = " (val = "^Int.toString (int_of_gi i)^")"

fun rdposotostr NONE = ""
  | rdposotostr (SOME (_,rd)) = " (pos = "^Position.toString (Bin_Reader.last_rd_pos rd)^")"
  
  
fun etostr (msg,(vo,po)) = msg ^ intotostr vo ^ natotostr po
fun eptostr (msg,(vo,po)) = msg ^ intotostr vo ^ rdposotostr po

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
  
fun verify_unsat_split a prf_next F_end it prf = let
  val _ = print ("c Verifying unsat (split certificate)\n");
  val vresult = Grat_Check.verify_unsat_split_impl_wrapper a prf_next F_end it prf ()
(*   val _ = print ("c Done\n"); *)
in
  (case vresult of
    Grat_Check.Inl e => print ("s ERROR: " ^ eptostr e)
  | Grat_Check.Inr _ => print ("s VERIFIED UNSAT"));
  
  print "\n"
end

fun verify_unsat a F_end it = let
  val _ = print ("c Verifying unsat\n");
  val vresult = Grat_Check.verify_unsat_impl_wrapper a F_end it ()
(*   val _ = print ("c Done\n"); *)
in
  (case vresult of
    Grat_Check.Inl e => print ("s ERROR: " ^ etostr e)
  | Grat_Check.Inr _ => print ("s VERIFIED UNSAT"));
  
  print "\n"
end


fun verify_sat a frml_end = let
  val _ = print ("c Verifying sat\n");
  val vresult = Grat_Check.verify_sat_impl_wrapper a frml_end ()
(*   val _ = print ("Done\n"); *)
in
  (case vresult of
    Grat_Check.Inl e => print ("s ERROR: " ^ etostr e)
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

type fbuf = Posix.IO.file_desc
(* Position, valid size, array containing     *)

val ESC = String.str (Char.chr 27)

fun check_split_unsat cnf_name lemmas_name proof_name = let
  val a = Array.array (1024,gi_of_int 0);
  
  val _ = print("c Using split proof mode, proof read buffer size is " ^ Position.toString (!Bin_Reader.buf_size) ^ "\n");
  
  val cnf_start = 1;
  val _ = print ("c Reading cnf\n");
  val (proof_start,a) = Dimacs_Parser.parse_dimacs_file_map_to_dynarray cnf_name gi_of_int (cnf_start,a);
  val _ = print ("c Reading lemmas\n");
  val (proof_end,a) = Dimacs_Parser.parse_dimacs_file_map_to_dynarray lemmas_name gi_of_int (proof_start,a);
  val _ = print ("c Done\n");

  fun prf_next rd = let val (v,rd) = Bin_Reader.rd32 rd; (*val _ = print (ESC^"[91m"^Int.toString v^ESC^"[0m ")*) in (gi_of_int v, rd) end
  
  val (fuel,rd) = Bin_Reader.openf(proof_name)
  val fuel = gn_of_int fuel
  val prf = (fuel, rd)
  
  val F_end = gn_of_int proof_start
  val it = gn_of_int proof_start
in
  verify_unsat_split a prf_next F_end it prf
end


fun check_unsat cnf_name grat_name = let
  val a = Array.array (1024,gi_of_int 0);
  
  val cnf_start = 1;
  val _ = print ("c Reading cnf\n");
  val (proof_start,a) = Dimacs_Parser.parse_dimacs_file_map_to_dynarray cnf_name gi_of_int (cnf_start,a);
  val _ = print ("c Reading proof\n");
  val (proof_end,a) = Dimacs_Parser.parse_dimacs_file_map_to_dynarray grat_name gi_of_int (proof_start,a);
  val _ = print ("c Done\n");

  
  val F_end = gn_of_int proof_start
  val it = gn_of_int proof_end
in
  verify_unsat a F_end it
end


fun check_sat cnf_name proof_name = let
  val a = Array.array (1024,gi_of_int 0);
  
  val cnf_start = 1;
  val _ = print ("c Reading cnf\n");
  val (proof_start,a) = Dimacs_Parser.parse_dimacs_file_map_to_dynarray cnf_name gi_of_int (cnf_start,a);
  val _ = print ("c Reading proof\n");
  val (proof_end,a) = Dimacs_Parser.parse_dimacs_file_map_to_dynarray proof_name gi_of_int (proof_start,a);
  val _ = print ("c Done\n");
  
  val frml_end = gn_of_int proof_start
  val _ = Dimacs_Parser.dyn_array_set a proof_end (gi_of_int 0)
in
  verify_sat a frml_end
end

(*datatype checker_mode = MODE_SAT | MODE_UNSAT | MODE_DUMP of int

fun checker mode cnf_name grat_name  = let
  val a = Array.array (1024,gi_of_int 0);
  
  val cnf_start = 1;
  val _ = print ("c Reading cnf\n");
  val (proof_start,a) = Dimacs_Parser.parse_dimacs_file_map_to_dynarray cnf_name gi_of_int (cnf_start,a);
  val _ = print ("c Reading proof\n");
  val (proof_end,a) = Dimacs_Parser.parse_dimacs_file_map_to_dynarray grat_name gi_of_int (proof_start,a);
  val _ = print ("c Done\n");
  val _ = print ("c Read " ^ Int.toString (proof_end-1) ^ " ints\n")
  val _ = print ("c Buffer " ^ Int.toString (Array.length a) ^ " ints\n")
  val _ = print ("c Last read: " ^ Int.toString (int_of_gi (Array.sub (a,proof_end - 1))) ^ "\n");
  
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
  
end*)

fun print_help () = (
  println("c Usage: " ^ CommandLine.name() ^ " options command");
  println("c where options are");
  println("c  --pbuf-size <size>                          Proof read buffer size in KiB");
  println("c where command is one of");
  println("c  unsat <cnf-file> <proof-file>               Check standard UNSAT certificate");
  println("c  unsat <cnf-file> <lemma-file> <proof-file>  Check split UNSAT certificate");
  println("c  sat <cnf-file> <lit-file>                   Check SAT certificate")
)

fun process_args ["sat",cnf_name,proof_name] = check_sat cnf_name proof_name
  | process_args ["unsat",cnf_name,lemmas_name,proof_name] = check_split_unsat cnf_name lemmas_name proof_name
  | process_args ["unsat",cnf_name,grat_name] = check_unsat cnf_name grat_name
  | process_args ("--pbuf-size"::size::rest) = (
      Bin_Reader.buf_size := valOf (Position.fromString size) * 1024;
      process_args rest
    )
(*  | process_args ["dump",cnf_name,grat_name,ofs] 
      = checker (MODE_DUMP (valOf (Int.fromString ofs))) cnf_name grat_name*)
  | process_args _ = (
      println("s ERROR: Invalid command line arguments");
      print_help()
    )    

fun main () = let
  val args = CommandLine.arguments ();
in
  process_args args
end


val _ = if MLton.isMLton then main() else ()
