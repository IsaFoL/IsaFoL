structure PAC_Parser =
struct

  open ParserCombinators
  open CharParser

  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??
  val int_of_string = valOf o IntInf.fromString

  fun print_ignore a = ()
  val var =
      (repeat1 letter && repeat1 digit) wth
                                        (fn (x, y) => (print_ignore (String.implode x ^ String.implode y ^"\n"); (String.implode x ^ String.implode y)))

  val signed_coefficient : IntInf.int charParser =
      (try (string "-" || string "+") && repeat1 digit) wth
      (fn (s, x) => (if s = "-" then int_of_string "~1" else int_of_string "1") * int_of_string (String.implode x))

  val unsigned_coefficient : IntInf.int charParser =
      (repeat1 digit) wth
      (fn x => int_of_string (String.implode x))
  val int_coefficient =
      signed_coefficient || unsigned_coefficient

  val uminus_coefficient : IntInf.int charParser =
      (string "-" || string "+") wth
      (fn x => if x = "-" then int_of_string "~1" else int_of_string "1")

  val coefficient : IntInf.int charParser =
      try (int_coefficient || uminus_coefficient)

  val var_product : string list charParser =
     ((var && repeat (string "*" >> var)) wth
                                          (fn (x, y) => (print_ignore x; (x :: y))))


  val monomial : (string list * IntInf.int) charParser =
      (((coefficient << opt (string "*")) && opt var_product) wth
       (fn (x, y) => (getOpt(y, []), x))) ||
      ((var_product wth
       (fn y => (y, (IntInf.fromInt 1)))))

  val polynom : (string list * IntInf.int) list charParser =
      repeat1 monomial


  val rule : string charParser =
      string "d +:" || string "+:" || string "d *:" || string "*:"

  val plus_rule : string charParser =
      (string "d +:" || string "+:") wth (fn x => (print_ignore x; x))

  val mult_rule : string charParser =
      string "d *:" || string "*:" wth (fn x => (print_ignore x; x))

  val lbl : IntInf.int charParser =
      repeat1 digit wth
              (fn x => (print_ignore ("\nlbl = " ^String.implode x ^"\n");
                        valOf (IntInf.fromString (String.implode x))))

  val input_poly : (IntInf.int * (string list * IntInf.int) list) charParser =
      ((lbl << space) && polynom) << string ";" <<  newLine


  val step_poly : ((string list * PAC_Checker.int) list PAC_Checker.pac_step) charParser =
      ((((lbl << spaces) && (plus_rule << spaces) && (lbl << string ", ") && (lbl << string ", ")
                        && polynom) << string ";" << newLine) wth
        (fn (lbl, (rule, (src1, (src2, poly)))) => 
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
         ) ) ||
      ((((lbl << space) && (mult_rule << spaces) && (lbl << string ", ") &&
           ((polynom << string ", ") wth (fn x => (print_ignore "now poly "; x)))
           && polynom) << string ";" << newLine)  wth
       (fn (lbl, (rule, (src1, (src2, poly)))) => 
           let val _ = 1 in 
           if rule = "d *:"
           then (PAC_Checker.MultD (PAC_Checker.nat_of_integer src1,
                                        (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) src2),
                                  PAC_Checker.nat_of_integer lbl,
                                      (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) poly)))
           else (PAC_Checker.Mult (PAC_Checker.nat_of_integer src1,
                                       (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) src2),
                                  PAC_Checker.nat_of_integer lbl,
                                      (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) poly))) end
        ) )

  val input_polys =
      repeat1 input_poly
  val step_poly =
      repeat1 step_poly


end
