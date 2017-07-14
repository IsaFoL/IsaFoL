(* Title: Explorer
   Initial author: Florian Haftmann
   Initial author: Fabian Immler
   License: ? ? ? ?
   From: The isabelle-dev mailing list. "Re: [isabelle-dev] The coming release of Isabelle2017"
   Link: http://www.mail-archive.com/isabelle-dev@mailbroy.informatik.tu-muenchen.de/msg07448.html
*)

theory Explorer
imports Main
keywords "explore" :: diag
begin

subsection {* Explore command *}

ML {*
fun split_clause t =
  let
    val (fixes, horn) = funpow_yield (length (Term.strip_all_vars t)) Logic.dest_all t;
    val assms = Logic.strip_imp_prems horn;
    val shows = Logic.strip_imp_concl horn;
  in (fixes, assms, shows) end;

fun isar_skeleton ctxt (fixes, assms, shows) =
  let
    val fixes_s = if null fixes then NONE
      else SOME ("fix " ^ space_implode " and "
        (map (fn (v, T) => v ^ " :: " ^ quote (Syntax.string_of_typ ctxt T)) fixes));
    val (_, ctxt') = Variable.add_fixes (map fst fixes) ctxt; 
    val assumes_s = if null assms then NONE
      else SOME ("assume " ^ space_implode " and "
        (map (quote o Syntax.string_of_term ctxt') assms))
    val shows_s = ("show " ^ (quote o Syntax.string_of_term ctxt') shows ^ " sorry")
    val s = cat_lines (map_filter I [fixes_s, assumes_s] @ [shows_s]);
  in
    s
  end;

fun explore st =
  let
    val { context, facts = _, goal } = Proof.goal st;
    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;
    val text = cat_lines
      ("proof -" :: separate "next" (map (isar_skeleton context) clauses) @ ["qed"]);
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

*}

subsection {* Examples *}

lemma
  "distinct xs \<Longrightarrow> length (filter (\<lambda>x. x = y) xs) \<le> 1"
  apply (induct xs)
  apply simp_all
  apply auto
  explore
    oops

end
