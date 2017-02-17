(*
  Author: Peter Lammich
*)


(*
  Hand optimized, quite fast and memory efficient parser for a superset of DIMACS CNF files.
  The rationale behind this parser is to be fast enough to parse big certificate files (several GiBs on 2016 standard laptop hardware),
  and at the same time being easy and structured enough to be (manually) verified. 
  
  Note that this parser belongs to the trusted code base of our formally verified SAT and UNSAT certification tools, as it 
  specifies the translation of a DIMACS-file to a sequence of numbers. 
  The second step, sequence of numbers to CNF formula, is actually specified inside the Isabelle/HOL formalization.
  
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

  TODO:
    Make this a functor parameterized over integer type and mapped element type!
    
*)
signature DIMACS_PARSER = sig
  (*
    Thrown on parsing error, contains textual error message.
  *)
  exception Parser_Error of string  

  (*
    Parse DIMACS input until given input stream is exhausted, and invoke callback for each parsed number.
  *)
  val parse_dimacs: TextIO.instream -> (int -> unit) -> unit
  
  (*
    parse_dimacs_map_to_dynarray istream f (size, a) |-> (new_size, new_a)
  
    Append a DIMACS input to a dynamically resized array, after mapping the numbers by f.
    The array is specified by the underlying array and the current (used) size.
    The function returns a new size and array.
    
    Invar for dynamically resized arrays: size <= Array.length a
  *)
  val parse_dimacs_map_to_dynarray: TextIO.instream -> (int -> 'a) -> (int * 'a Array.array) -> (int * 'a Array.array)
  
  (* Convenience versions with file names *)
  val parse_dimacs_file: string -> (int -> unit) -> unit
  val parse_dimacs_file_map_to_dynarray: string -> (int -> 'a) -> (int * 'a Array.array) -> (int * 'a Array.array)
  

  
  (* Set ith element of a to x, resizing a as necessary, filling new space with xs. TODO: Should go to some dyn-array library! *)
  val dyn_array_set: 'a Array.array -> int -> 'a -> 'a Array.array
  
end

structure Dimacs_Parser : DIMACS_PARSER = struct
  exception Parser_Error of string  

  fun parse_dimacs istream accept_num_callback = let
    fun is_digit c = c >= #"0" andalso c <= #"9"
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
    
    fun rd state =
      case TextIO.input1(istream) of
        NONE => (* EOF *) (
          case state of
            NUM => accept_num_callback (!sgn * !num)
          | NEG => raise Parser_Error "Lone MINUS before EOF"
          | _ => ()
        )
      | SOME c => (* Character *) (
          case state of 
            NUM => 
                   if is_digit c then ( num := (!num) * 10 + digit_of_char c; rd NUM )
              else if is_space c then ( accept_num_callback (!sgn * !num); rd INIT )
              else raise Parser_Error ("Numbers must be terminated by space or EOF, but found character '" ^ Char.toString c ^ "'")
          | NEG => 
                   if is_digit c then ( sgn := ~1; num := digit_of_char c; rd NUM) 
              else raise Parser_Error "Expected number after MINUS"
          | INIT =>
                   if is_digit c then ( sgn := 1; num := digit_of_char c; rd NUM )
              else if c = #"-" then rd NEG 
              else if is_space c then rd INIT
              else if is_alpha c then rd COMMENT 
              else raise Parser_Error ("Unexpected character in non-ignore position '" ^ Char.toString c ^ "'")
          | COMMENT => if c = #"\n" then rd INIT else rd COMMENT
        )

  in
    rd INIT
  end

  
  fun dyn_array_set a i x = let
    val len = Array.length a;
    val a = 
      if i < len then a else
      let
        val size = Int.max (i+1,3*len div 2);
        val b = Array.array (size, x)
        val _ = Array.copy {di=0, dst=b,src=a};
      in 
        b
      end
    val _ = Array.update (a,i,x)
  in a end
  
  
  fun parse_dimacs_map_to_dynarray istream f (size, a) = let
    val idx = ref size
    val arr = ref a

    fun accept_num x = ( arr := dyn_array_set (!arr) (!idx) (f x); idx := !idx + 1 )

    val _ = parse_dimacs istream accept_num    
  in
    (!idx,!arr)
  end

  
  fun parse_dimacs_file file_name accept_num_callback = let
    val istream = TextIO.openIn file_name
    val _ = parse_dimacs istream accept_num_callback
    val _ = TextIO.closeIn istream
  in 
    ()
  end
  
  fun parse_dimacs_file_map_to_dynarray file_name f da = let
    val istream = TextIO.openIn file_name
    val da = parse_dimacs_map_to_dynarray istream f da
    val _ = TextIO.closeIn istream
  in 
    da
  end  
  
  
end
