(* 

LICENSE: ? ? ? ? 
FROM: http://www.mail-archive.com/isabelle-dev@mailbroy.informatik.tu-muenchen.de/msg07448.html

FABIAN IMMLER

A while ago, Florian Haftmann sent a command that does something like this to the mailing list [1]. I attach a version that works with current Isabelle2016-1 (not sure if I got all the modifications right, but it seems to work at least on the example in the .thy file).

Fabian

[1] http://www.mail-archive.com/isabelle-dev@mailbroy.informatik.tu-muenchen.de/msg04443.html


> Am 09.07.2017 um 16:58 schrieb Lawrence Paulson <lp15@cam.ac.uk>:
> 
> What I’m requesting requires no sophistication at all. It is merely to automate what we currently do by copying from one window and pasting to another, while inserting “fix”, “assume” and “show” in the obvious places.
> Larry
> 
>> On 9 Jul 2017, at 16:32, Lars Hupel <hupel@in.tum.de> wrote:
>> 
>> I currently supervise a student who's investigating proof refactoring. One possible outcome of this would be a tool that also does what you suggested. It's a little too early to tell, though.
> 
> _______________________________________________
> isabelle-dev mailing list
> isabelle-dev@in.tum.de
> https://mailmanbroy.informatik.tu-muenchen.de/mailman/listinfo/isabelle-dev



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
