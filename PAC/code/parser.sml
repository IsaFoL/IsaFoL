structure PAC_Parser =
struct

  exception Parser_Error of string

  fun is_digit c = c >= #"0" andalso c <= #"9";
  fun is_zero c = (c = #"0");
  fun digit_of_char c = Char.ord c - Char.ord #"0";

  fun is_alpha c =
      c >= #"a" andalso c <= #"z"
      orelse c >= #"A" andalso c <= #"Z";

  fun is_space c =
      c = #" " orelse c = #"\t" orelse c = #"\n" orelse c = #"\r";

  fun is_separator c =
      c = #"*" orelse c = #"," orelse c = #";" orelse c = #"+" orelse c = #"-";

  fun print _ = ();
  fun rev2 a = rev a;

  fun skip_spaces istream =
      (print "skip space";
       if TextIO.lookahead(istream) = SOME #" "
      then (TextIO.input1(istream); skip_spaces istream)
      else ())


  fun parse_natural istream =
      let
        val _ = print "parse_number\n"
        val num = ref (IntInf.fromInt 0);
        val seen_one_digit = ref false;
        fun parse_aux () =
            let val c = TextIO.lookahead istream
            in
              if (is_space (valOf c) orelse is_separator (valOf c))
              then (print ("number sep = " ^ String.implode [(valOf c)]))
              else
                case TextIO.input1(istream) of
                    NONE => raise Parser_Error "no number found"
                  | SOME c =>
                    if is_digit c
                    then (seen_one_digit := true;
                          num := IntInf.+ (IntInf.*(!num, IntInf.fromInt 10), IntInf.fromInt (digit_of_char c));
                          parse_aux ())
                    else raise Parser_Error ("no number found, found " ^ String.implode [c])
            end
      in
        (parse_aux ();
         if !seen_one_digit = false
         then raise Parser_Error ("no number digit")
         else !num)
      end

  fun parse_var istream =
      let
        val _ = print "parse_var\n"
        val num = ref [];
        fun parse_aux () =
            let val c = TextIO.lookahead istream
            in
              if (is_space (valOf c) orelse is_separator (valOf c))
              then (print ("var sep = " ^ String.implode [(valOf c)]))
              else
                case TextIO.input1(istream) of
                    NONE => raise Parser_Error "no char found"
                  | SOME c =>
                    (num := c :: (!num); parse_aux ())
            end
      in
        (parse_aux ();
         if !num = []
         then raise Parser_Error "no variable found"
         else (print (String.implode (rev (!num))); String.implode (rev (!num))))
      end;

  fun parse_vars_only_monom istream = (* can start with /*/ *)
      let
        val _ = print "parse_vars_only_monom\n"
        val vars = ref [];
        fun parse_aux () =
            if TextIO.lookahead(istream) = SOME #"," orelse TextIO.lookahead(istream) = SOME #";"
               orelse TextIO.lookahead(istream) = SOME #"-" orelse TextIO.lookahead(istream) = SOME #"+"
            then (print ("parse_vars_only_monom, sep =" ^ String.implode [valOf (TextIO.lookahead(istream))] ^ "\n"))
            else if TextIO.lookahead(istream) = SOME #"*"
            then
              (ignore (TextIO.input1(istream));
               vars := parse_var istream :: (!vars);
               parse_aux ())
            else
              (vars := parse_var istream :: (!vars);
               parse_aux ())
      in
        parse_aux ();
        rev2 (!vars)
      end;

  fun parse_full_monom istream =
      let
        val _ = print "parse_full_monom\n"
        val num = ref 1;
        val vars = ref [];
        val next_token = ref NONE;
      in
        (
          next_token := TextIO.lookahead(istream);
          print ("parse_full_monom/next token 1 = '" ^String.implode [valOf (!next_token)] ^ "'\n");
          (case !next_token of
               SOME #"-" =>
               (ignore (TextIO.input1 istream);
                num := ~1)
             | SOME #"+" => ignore (TextIO.input1 istream)
             | _ => ());
          next_token := TextIO.lookahead(istream);
          print ("parse_full_monom/next token 2 = '" ^String.implode [valOf (!next_token)] ^ "'\n");
          if !next_token <> NONE andalso is_digit (valOf (!next_token))
          then num := !num * parse_natural istream
          else ();
          vars := parse_vars_only_monom istream;
          next_token := TextIO.lookahead(istream);
          print ("parse_full_monom/next token 3 = '" ^String.implode [valOf (!next_token)] ^ "'\n");
          (!vars, !num)
        )
      end;

  fun parse_comma istream () =
      let
        val c1 = TextIO.input1(istream)
        val c2 = TextIO.input1(istream)
      in
        if valOf c1 <> #"," orelse valOf c2 <> #" "
        then raise Parser_Error ("unrecognised ', ', found '" ^ String.implode [valOf c1, valOf c2] ^ "'")
        else ()
      end

          
  fun parse_polynom istream : (string list * IntInf.int) list =
      let
        val _ = print "parse_poly\n"
        val monoms = ref [];
        fun parse_aux () =
            if TextIO.lookahead(istream) = SOME #"," orelse TextIO.lookahead(istream) = SOME #";"
            then print ("parse_poly finished"  ^ String.implode [valOf (TextIO.lookahead(istream))] ^ "\n")
            else (monoms := parse_full_monom istream :: !monoms;
                 parse_aux ())
      in
        (parse_aux ();
        rev2 (!monoms))
      end

  fun parse_rule istream =
      let val del = ref false;
      in
        skip_spaces istream;
        if TextIO.lookahead(istream) = SOME #"d"
        then (TextIO.input1(istream); del := true)
        else ();
        skip_spaces istream;
        case TextIO.lookahead(istream) of
            SOME #"+" =>
            if !del then (ignore (TextIO.input1 istream); ignore (TextIO.input1 istream); "d +:")
            else (ignore (TextIO.input1 istream); ignore (TextIO.input1 istream); "+:")
          | SOME #"*" =>
            if !del then (ignore (TextIO.input1 istream); ignore (TextIO.input1 istream); "d *:")
            else (ignore (TextIO.input1 istream); ignore (TextIO.input1 istream); "*:")
          | SOME c => raise Parser_Error ("unrecognised rule '" ^ String.implode [c] ^ "'")
      end

  fun parse_EOL istream () =
      let
        val c1 = TextIO.input1(istream)
        val c2 = TextIO.input1(istream)
      in
        if c1 <> NONE andalso c2 <> NONE andalso (valOf c1 <> #";" orelse valOf c2 <> #"\n")
        then raise Parser_Error ("unrecognised EOL '" ^ String.implode [valOf c1, valOf c2] ^ "'")
        else ()
      end
 
  fun parse_step istream =
      let
        val lbl = parse_natural istream;
        val _ = print ("label = " ^ IntInf.toString lbl);
        val rule = parse_rule istream;
        val _ = skip_spaces istream;
      in
        if rule = "d +:" orelse rule = "+:"
        then
          let
            val src1 = parse_natural istream;
            val _ = parse_comma istream ();
            val src2 = parse_natural istream;
            val _ = parse_comma istream ();
            val poly = parse_polynom istream;
            val _ = parse_EOL istream ();
          in
            if rule = "d +:"
            then (PAC_Checker.AddD (
                     PAC_Checker.nat_of_integer src1,
                     PAC_Checker.nat_of_integer src2,
                     PAC_Checker.nat_of_integer lbl,
                     (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) poly)))
            else (PAC_Checker.Add (PAC_Checker.nat_of_integer src1,
                                   PAC_Checker.nat_of_integer src2,
                                   PAC_Checker.nat_of_integer lbl,
                                   (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) poly)))
          end
        else
          let
            val src1 = parse_natural istream;
            val _ = parse_comma istream ();
            val src2 = parse_polynom istream;
            val _ = parse_comma istream ();
            val poly = parse_polynom istream;
            val _ = parse_EOL istream ();
          in
           if rule = "d *:"
           then (PAC_Checker.MultD (PAC_Checker.nat_of_integer src1,
                                        (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) src2),
                                  PAC_Checker.nat_of_integer lbl,
                                      (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) poly)))
           else (PAC_Checker.Mult (PAC_Checker.nat_of_integer src1,
                                       (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) src2),
                                  PAC_Checker.nat_of_integer lbl,
                                      (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) poly)))
          end
      end

  fun step_polys istream =
      let
        val polys = ref [];
        fun parse_aux () =
            if TextIO.lookahead(istream) = NONE
            then rev (!polys)
            else (polys := parse_step istream :: (!polys);
                  skip_spaces istream;
                  parse_EOL istream;
                  parse_aux ())
      in
        parse_aux ()
      end

  fun input_poly istream : IntInf.int * (string list * IntInf.int) list =
      let val a = parse_natural istream
          val _ = skip_spaces istream
          val b = (parse_polynom istream)
          val _ = print ("parsed " ^ IntInf.toString a ^"\n")
      in (a,b) end

  fun input_polys istream =
      let
        val polys = ref [];
        fun parse_aux () =
            if TextIO.lookahead(istream) = NONE
            then rev (!polys)
            else (polys := input_poly istream :: (!polys);
                  parse_EOL istream ();
                  parse_aux ())
      in
        parse_aux ()
      end

end
