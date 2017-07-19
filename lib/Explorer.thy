(* Title: Explorer
   Initial author: Florian Haftmann
   Initial author: Fabian Immler
   License: ? ? ? ?
   From: The isabelle-dev mailing list. "Re: [isabelle-dev] The coming release of Isabelle2017"
   Link: http://www.mail-archive.com/isabelle-dev@mailbroy.informatik.tu-muenchen.de/msg07448.html
*)

theory Explorer
imports Main
keywords "explore" "explore_have" :: diag
begin

subsection {* Explore command *}

ML {*
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

fun isar_skeleton ctxt is_have (fixes, assms, shows) =
  let
    val kw_fix = if is_have then "  for " else "  fix "
    val kw_assume = if is_have then "  if " else "  assume "
    val kw_goal = if is_have then "  have " else "  show "
    val fixes_s = if null fixes then NONE
      else SOME (kw_fix ^ space_implode " and "
        (map (fn (v, T) => v ^ " :: " ^ quote (Syntax.string_of_typ ctxt T)) fixes));
    val (_, ctxt') = Variable.add_fixes (map fst fixes) ctxt; 
    val assumes_s = if null assms then NONE
      else SOME (kw_assume ^ space_implode_with_line_break
        (map (quote o Syntax.string_of_term ctxt') assms))
    val shows_s = (kw_goal ^ (quote o Syntax.string_of_term ctxt') shows)
    val s = 
      if is_have
      then cat_lines (shows_s :: map_filter I [assumes_s, fixes_s] @ ["  sorry"])
      else cat_lines (map_filter I [fixes_s, assumes_s] @ [shows_s ^ " sorry"]);
  in
    s
  end;

fun explore st =
  let
    val { context, facts = _, goal } = Proof.goal st;
    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;
    val text = cat_lines
      ("proof -" :: separate "next" (map (isar_skeleton context false) clauses) @ ["qed"]);
    val message = Active.sendback_markup_properties [] text;
  in
    (st |> tap (fn _ => Output.information message))
  end

val explore_cmd =
  Toplevel.keep_proof (K () o explore o Toplevel.proof_of)

val _ =
  Outer_Syntax.command @{command_keyword "explore"}
    "explore current goal state as Isar proof"
    (Scan.succeed explore_cmd)

fun explore_have st =
  let
    val { context, facts = _, goal } = Proof.goal st;
    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;
    val text = cat_lines
      (separate "" (map (isar_skeleton context true) clauses));
    val message = Active.sendback_markup_properties [] text;
  in
    (st |> tap (fn _ => Output.information message))
  end


val explore_have_cmd =
  Toplevel.keep_proof (K () o explore_have o Toplevel.proof_of)

val _ =
  Outer_Syntax.command @{command_keyword "explore_have"}
    "explore current goal state as Isar proof with have, if and for"
    (Scan.succeed explore_have_cmd)
*}

subsection {* Examples *}

lemma
  "distinct xs \<Longrightarrow> length (filter (\<lambda>x. x = y) xs) \<le> 1"
  apply (induct xs)
  apply simp_all
  apply auto
  explore
  explore_have
  oops

end
