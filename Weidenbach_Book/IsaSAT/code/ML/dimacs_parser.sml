(*
  Author: Mathias Fleury, based on Peter Lammich's dimacs_parser.
*)


(*

  Informal description:
    The parser reads a stream of decimal ASCII encoded integers, separated by spaces, tabs, or newlines.
    If an alphabetic character is found, everything up to the next newline is ignored.
    After numbers, only spaces, tabs, newlines, or EOF is allowed.

  Formal description of grammar:
    dimacs  := INIT
    INIT    := <digit> NUM | '-' NEG | <space> INIT | <alpha> COMMENT
    NUM     := <digit> NUM | <space> INIT
    NEG     := <digit> NUM
    COMMENT := '\n' INIT | [^\n] COMMENT
    <digit> := [0-9]
    <space> := [ \t\n\r]
    <alpha> := [a-zA-Z]

*)
signature DIMACS_PARSER = sig
  (*
    Thrown on parsing error, contains textual error message.
  *)
  exception Parser_Error of string

  (*
    Parse DIMACS input until given input stream is exhausted, and invoke callback for each parsed number.
  *)
  val parse_dimacs: TextIO.instream -> (int -> 'a) -> ('a List.list List.list)

  (*
    parse_dimacs_map_to_dynarray istream f (size, a) |-> (new_size, new_a)

    Append a DIMACS input to a dynamically resized array, after mapping the numbers by f.
    The array is specified by the underlying array and the current (used) size.
    The function returns a new size and array.

    Invar for dynamically resized arrays: size <= Array.length a
  *)
  val parse_dimacs_map_to_list: TextIO.instream -> (int -> 'a) -> ('a List.list List.list)

  (* Convenience versions with file names *)
  val parse_dimacs_file: string -> (int -> 'a) -> ('a List.list List.list)
  val parse_dimacs_file_map_to_list: string -> (int -> 'a) -> ('a List.list List.list)

end

structure Dimacs_Parser : DIMACS_PARSER = struct
  exception Parser_Error of string

  fun parse_dimacs istream f = let
    fun is_digit c = c > #"0" andalso c <= #"9"
    fun is_zero c = (c = #"0")
    fun digit_of_char c = Char.ord c - Char.ord #"0"

    fun is_alpha c =
             c >= #"a" andalso c <= #"z"
      orelse c >= #"A" andalso c <= #"Z"

    fun is_space c =
      c = #" " orelse c = #"\t" orelse c = #"\n" orelse c = #"\r"


    datatype state = INIT | COMMENT | NEG | NUM

    (* Current number and sign, it's much more efficient (MLton 20100608) to NOT store this in NUM state! *)
    val num = ref 0
    val sgn = ref 1
    val clause = ref []
    fun rd state =
      case TextIO.input1(istream) of
        NONE => (* EOF *) (
          case state of
            NUM => []
          | NEG => raise Parser_Error "Lone MINUS before EOF"
          | _ => []
        )
       | SOME c => (* Character *) (
          case state of
            NUM =>
            if is_digit c orelse is_zero c then (num := (!num) * 10 + digit_of_char c; rd NUM)
            else if is_space c then (clause := f (!sgn * !num) :: !clause; rd INIT)
            else raise Parser_Error ("Numbers must be terminated by space or EOF, but found character '" ^ Char.toString c ^ "'")
          | NEG =>
            if is_digit c then ( sgn := ~1; num := digit_of_char c; rd NUM)
            else raise Parser_Error "Expected number after MINUS"
          | INIT =>
            if is_zero c then (let val cls = !clause in clause := []; num := 0; sgn := 1; rev cls :: rd INIT end)
            else if is_digit c then ( sgn := 1; num := digit_of_char c; rd NUM )
            else if c = #"-" then rd NEG
            else if is_space c then rd INIT
            else if is_alpha c then rd COMMENT
            else (raise Parser_Error ("Unexpected character in non-ignore position '" ^ Char.toString c ^ "'"))
          | COMMENT => if c = #"\n" then rd INIT else rd COMMENT
        )

  in
    rd INIT
  end



  fun parse_dimacs_map_to_list istream f = let
  in
    parse_dimacs istream f
  end


  fun parse_dimacs_file file_name f = let
    val istream = TextIO.openIn file_name
    val a = parse_dimacs istream f
    val _ = TextIO.closeIn istream
  in
    a
  end

  fun parse_dimacs_file_map_to_list file_name f = let
    val istream = TextIO.openIn file_name
    val da = parse_dimacs_map_to_list istream f
    val _ = TextIO.closeIn istream
  in
    da
  end


end
