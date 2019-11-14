fun println x = print (x ^ "\n")


fun print_help () = (
  println "TODO"
)

fun readfile istream =
    let val a = TextIO.inputLine istream
    in if a = NONE then [] else valOf a :: readfile istream
    end


fun print_poly [] = (print " + 0")
  | print_poly ((i, m) :: xs) =
    (print (IntInf.toString i ^" * ");
     map print m;
    print_poly xs)
fun print_input_poly (lbl, poly) =
    (println (Int.toString lbl); print_poly poly)

val extract = (fn x => if Sum.isL x then (println (Sum.outL x); raise Sum.Sum) else Sum.outR x)
fun parse_polys_file file_name = let
  val istream = TextIO.openIn file_name
  val a = map (fn x =>
                  let val (lbl, poly) = (extract (CharParser.parseString PAC_Parser.input_poly x))
                  in
                    (PAC_Checker.nat_of_integer lbl,
                         map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) poly)
                  end)
              (readfile istream)
  val _ = TextIO.closeIn istream
in
  foldl (fn ((lbl, a), b) => PAC_Checker.pAC_update_impl lbl a b ()) (PAC_Checker.pAC_empty_impl ()) a
end

fun parse_pac_file file_name = let
  val istream = TextIO.openIn file_name
  val a = map (fn x =>
                  let val a = (Sum.outR (CharParser.parseString PAC_Parser.step_poly x))
                  in
                  List.hd (a)
                  end)
              (readfile istream)
  val _ = TextIO.closeIn istream
in
  a
end

fun parse_spec_file file_name = let
  val istream = TextIO.openIn file_name
  val a = map (fn x =>
                  let val a = (Sum.outR (CharParser.parseString PAC_Parser.polynom x))
                  in
                  a
                  end)
              (readfile istream)
  val _ = TextIO.closeIn istream
in
  case a of
      [a] => (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) a)
end


fun checker [polys, pac, spec] = let
  val _ = println "start";
  val timer = Timer.totalCPUTimer ();
  val problem = parse_polys_file polys;
  val _ = println "polys parsed\n******************"
  val timer = Timer.totalCPUTimer ();
  val pac : ((string list * PAC_Checker.int) list PAC_Checker.pac_step) list = parse_pac_file pac;
  val pac : ((string list * PAC_Checker.int) list PAC_Checker.pac_step) array = (Array.fromList pac)
  val _ = println "pac parsed"
  val (spec : ((string list * PAC_Checker.int) list)) = parse_spec_file spec;
  val _ = println "spec parsed";
  val end_of_init = Timer.checkCPUTimes timer;
  val _ = print (Int.toString (MLton.size problem));
  val _ = println "Now checking";
  val (b, _) = PAC_Checker.full_checker_l_impl spec problem pac ();
  val _ = if PAC_Checker.is_cfound b then println "s SUCCESSFULL"
          else if (PAC_Checker.is_cfailed b) = false then println "s FAILED, but correct PAC"
          else (println "s FAILED!!!!!!!"; println (PAC_Checker.implode (PAC_Checker.the_error b)))
  (* val timer = Timer.totalCPUTimer () *)
  (* val (SAT, stat) = SAT_Solver.isaSAT_code (not norestart, (not noreduction, nounbounded)) problem (); *)
  (* val end_of_processing = Timer.checkCPUTimes timer *)
  (* val _ = (if print_stats then print_stat stat end_of_init end_of_processing else ()); *)
  (* val _ = *)
  (*       (case SAT of *)
  (*            NONE => print "s UNSATISFIABLE\n" *)
  (*          | SOME SAT => (if print_modelb then ignore (print_model SAT) else (); print "s SATISFIABLE\n")) *)
  in
    ()
end

fun process_args [] = print_help() 
  | process_args [polys, pac, spec] =
    checker [polys, pac, spec]

fun main () = let
  val args = CommandLine.arguments ();
in
  process_args args
end


val _ = if MLton.isMLton then main() else ()
