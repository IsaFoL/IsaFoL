(* Title: Explorer
   Initial author: Florian Haftmann
   Initial author: Fabian Immler
   License:    
   From: The isabelle-dev mailing list. "Re: [isabelle-dev] The coming release of Isabelle2017"
   Link: http://www.mail-archive.com/isabelle-dev@mailbroy.informatik.tu-muenchen.de/msg07448.html
*)

theory Explorer
imports Main
keywords "explore" "explore_have" "explore_lemma" :: diag
begin

subsection {* Explore command *}

ML {*
datatype explore = HAVE_IF | ASSUME_SHOW | ASSUMES_SHOWS

fun split_clause t =
  let
    val (fixes, horn) = funpow_yield (length (Term.strip_all_vars t)) Logic.dest_all t;
    val assms = Logic.strip_imp_prems horn;
    val shows = Logic.strip_imp_concl horn;
  in (fixes, assms, shows) end;

fun space_implode_with_line_break l =
  if length l > 1 then
     "\n    " ^ space_implode  " and\n    " l
  else
    space_implode  " and\n    " l

fun keyword_fix HAVE_IF =          "  for "
  | keyword_fix ASSUME_SHOW =      "  fix "
  | keyword_fix ASSUMES_SHOWS =    "  fixes "

fun keyword_assume HAVE_IF =       "  if "
  | keyword_assume ASSUME_SHOW =   "  assume "
  | keyword_assume ASSUMES_SHOWS = "  assumes "

fun keyword_goal HAVE_IF =        ""
  | keyword_goal ASSUME_SHOW =    "  show "
  | keyword_goal ASSUMES_SHOWS =  "  shows "

fun isar_skeleton ctxt aim (fixes, assms, shows) =
  let
    val kw_fix = keyword_fix aim
    val kw_assume = keyword_assume aim
    val kw_goal = keyword_goal aim
    val fixes_s = if null fixes then NONE
      else SOME (kw_fix ^ space_implode " and "
        (map (fn (v, T) => v ^ " :: " ^ quote (Syntax.string_of_typ ctxt T)) fixes));
    val (_, ctxt') = Variable.add_fixes (map fst fixes) ctxt; 
    val assumes_s = if null assms then NONE
      else SOME (kw_assume ^ space_implode_with_line_break
        (map (quote o Syntax.string_of_term ctxt') assms))
    val shows_s = (kw_goal ^ (quote o Syntax.string_of_term ctxt') shows)
    val s = 
      (case aim of
        HAVE_IF =>  (map_filter I [fixes_s], map_filter I [assumes_s], shows_s)
      | ASSUME_SHOW =>  (map_filter I [fixes_s], map_filter I [assumes_s], shows_s ^" sorry")
      | ASSUMES_SHOWS =>   (map_filter I [fixes_s], map_filter I [assumes_s], shows_s));
  in
    s
  end;

fun generate_text ASSUME_SHOW context clauses =
  let val lines = clauses
      |> map (isar_skeleton context ASSUME_SHOW)
      |> map (fn (a, b, c) => a @ b @ [c])
      |> map cat_lines
  in
  ("proof -" :: separate "next" lines @ ["qed"])
 end
 | generate_text HAVE_IF context clauses =
    let
      val raw_lines = map (isar_skeleton context HAVE_IF) clauses
      fun treat_line (fixes_s, assumes_s, shows_s) =
        let val combined_line = [shows_s] @ assumes_s @ fixes_s |> cat_lines
        in
          "have " ^ combined_line ^ "\nproof\n  show thesis sorry\nqed"
       end
      val raw_lines_with_proof_body = map treat_line raw_lines
    in
      separate "\n" raw_lines_with_proof_body
    end
 | generate_text ASSUMES_SHOWS context clauses =
    let
      val raw_lines = map (isar_skeleton context ASSUMES_SHOWS) clauses
      fun treat_line (fixes_s, assumes_s, shows_s) =
        let val combined_line = assumes_s @ fixes_s @ [shows_s] |> cat_lines
        in
          "lemma\n" ^ combined_line ^ "\nproof\n  show thesis sorry\nqed"
       end
      val raw_lines_with_lemma_and_proof_body = map treat_line raw_lines
    in
      separate "\n" raw_lines_with_lemma_and_proof_body
    end;

fun explore aim st =
  let
    val { context, facts = _, goal } = Proof.goal st;
    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;
    val text = cat_lines (generate_text aim context clauses);
    val message = Active.sendback_markup_properties [] text;
  in
    (st |> tap (fn _ => Output.information message))
  end

val explore_cmd =
  Toplevel.keep_proof (K () o explore ASSUME_SHOW o Toplevel.proof_of)

val _ =
  Outer_Syntax.command @{command_keyword "explore"}
    "explore current goal state as Isar proof"
    (Scan.succeed explore_cmd)

val explore_have_cmd =
  Toplevel.keep_proof (K () o explore HAVE_IF o Toplevel.proof_of)

val _ =
  Outer_Syntax.command @{command_keyword "explore_have"}
    "explore current goal state as Isar proof with have, if and for"
    (Scan.succeed explore_have_cmd)

val explore_lemma_cmd =
  Toplevel.keep_proof (K () o explore ASSUMES_SHOWS o Toplevel.proof_of)

val _ =
  Outer_Syntax.command @{command_keyword "explore_lemma"}
    "explore current goal state as Isar proof with have, if and for"
    (Scan.succeed explore_lemma_cmd)
*}

subsection {* Examples *}

lemma
  "distinct xs \<Longrightarrow> P xs \<Longrightarrow> length (filter (\<lambda>x. x = y) xs) \<le> 1"
  apply (induct xs)
(*   apply simp_all
  apply auto *)
  explore
  explore_have
  explore_lemma
  oops

end
