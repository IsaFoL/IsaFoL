
fun main () = let
  val args = CommandLine.arguments ();
  
  val ([filename]) = args;
  
  val a = Array.array (1024,0);
  val (size,a) = Dimacs_Parser.parse_dimacs_file_map_to_dynarray filename (fn x => x) (0,a)
  val _ = print ("Read " ^ Int.toString(size) ^ " elements, buffer size " ^ Int.toString (Array.length a) ^ " elements\n")
  
  fun dump i = 
    if i < size then 
      let
        val x = Array.sub (a, i)
        val _ = print (Int.toString x)
      in
        (if x=0 then print "\n" else print " "); dump (i+1)
      end
    else
      print "\n"
  
  val _ = dump 0
in
  ()
end;

(*
datatype state =
  INIT | COMMENT | NEG | NUM of int

datatype state2 =
  NUM2 | NEG2 | INIT2 | COMMENT2


fun main2 () = let
  val args = CommandLine.arguments ();
  (*val args = map (fn x => (x, Int.fromString x)) args*)
  
  val ([filename]) = args;
  
  val istream = TextIO.openIn(filename);
  
  val arr = ref (Array.array (1024,0 : int));
  val idx = ref 0
  val num = ref 0

  fun accept_num n = (
(*     arr := aset (!arr) (!idx) n; *)
    idx := !idx + 1
  )
  
  fun is_digit c = c >= #"0" andalso c <= #"9"
  fun digit_of_char c = Char.ord c - Char.ord #"0"
  
  fun rd state =
    case TextIO.input1(istream) of
      NONE => (* EOF *) (
        case state of
          NUM2 => accept_num (!num)
        | _ => ()
      )
    | SOME c => (* Character *) (
        case state of 
          NUM2 => if is_digit c then ( num := (!num) * digit_of_char c; rd NUM2) else ( accept_num (!num); rd INIT2 )
        | NEG2 => if is_digit c then ( num := ~ (digit_of_char c); rd NUM2) else raise ParserError "Expected number after MINUS"
        | INIT2 =>
                 if is_digit c then ( num := digit_of_char c; rd NUM2 )
            else if c = #"-" then rd NEG2 
            else if c = #"c" then rd COMMENT2 
            else rd INIT2
        | COMMENT2 => if c = #"\n" then rd INIT2 else rd COMMENT2
      )

  val _ = rd INIT2
  
  val _ = print ("Read " ^ Int.toString(!idx) ^ " elements, buffer size " ^ Int.toString (Array.length (!arr)) ^ " elements\n")
  
  val _ = TextIO.closeIn(istream);
  
in () end;




fun main () = let
  val args = CommandLine.arguments ();
  (*val args = map (fn x => (x, Int.fromString x)) args*)
  
  val ([filename]) = args;
  
  val istream = TextIO.openIn(filename);
  
  val arr = ref (Array.array (1024,0 : int));
  val idx = ref 0

  fun accept_num n = (
(*     arr := aset (!arr) (!idx) n; *)
    idx := !idx + 1
  )
  
  fun is_digit c = c >= #"0" andalso c <= #"9"
  fun digit_of_char c = Char.ord c - Char.ord #"0"
  
  fun rd state =
    case TextIO.input1(istream) of
      NONE => (* EOF *) (
        case state of
          NUM x => accept_num x
        | _ => ()
      )
    | SOME c => (* Character *) (
        case state of 
          NUM n => if is_digit c then rd (NUM (n * digit_of_char c)) else ( accept_num n; rd INIT )
        | INIT =>
                 if is_digit c then rd (NUM (digit_of_char c))
            else if c = #"-" then rd NEG 
            else if c = #"c" then rd COMMENT 
            else rd INIT
        | COMMENT => if c = #"\n" then rd INIT else rd COMMENT
        | NEG => if is_digit c then rd (NUM (~ (digit_of_char c))) else raise ParserError "Expected number after MINUS"
      )

  val _ = rd INIT
  
  val _ = print ("Read " ^ Int.toString(!idx) ^ " elements, buffer size " ^ Int.toString (Array.length (!arr)) ^ " elements\n")
  
  val _ = TextIO.closeIn(istream);
  
in () end;
*)

main ();
