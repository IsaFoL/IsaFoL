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
fun parse_input_pac_file file_name = let
  val istream = TextIO.openIn file_name
  val a = map (fn x =>
                  let val a = (extract (CharParser.parseString PAC_Parser.input_poly x))
                  in
                  ((*print "\npoly = ";
                   print_input_poly a;*)
                   a)
                  end)
              (readfile istream)
  val _ = TextIO.closeIn istream
in
  a
end

fun parse_pac_file file_name = let
  val istream = TextIO.openIn file_name
  val a = map (fn x =>
                  let val a = (extract (CharParser.parseString PAC_Parser.step_poly x))
                  in
                  (a)
                  end)
              (readfile istream)
  val _ = TextIO.closeIn istream
in
  a
end

fun parse_spec_file file_name = let
  val istream = TextIO.openIn file_name
  val a = map (fn x =>
                  let val a = (extract (CharParser.parseString PAC_Parser.polynom x))
                  in
                  (a)
                  end)
              (readfile istream)
  val _ = TextIO.closeIn istream
in
  case a of
      [a] => a
end
fun checker [polys, pac, spec] = let
  val _ = println "start"
  val timer = Timer.totalCPUTimer ()
  val problem = parse_input_pac_file polys;
  val _ = println "polys parsed\n******************"
  val timer = Timer.totalCPUTimer ()
  val problem = parse_pac_file pac;
  val _ = println "pac parsed"
  val problem = parse_spec_file spec;
  val _ = println "spec parsed"
  val end_of_init = Timer.checkCPUTimes timer
  val _ = print (Int.toString (MLton.size problem))
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
