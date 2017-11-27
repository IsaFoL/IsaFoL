(* Title: Explorer
   Initial author: Florian Haftmann
   Initial author: Fabian Immler
   Maintainer: Mathias Fleury
   License:    
   From: The isabelle-dev mailing list. "Re: [isabelle-dev] The coming release of Isabelle2017"
   Link: http://www.mail-archive.com/isabelle-dev@mailbroy.informatik.tu-muenchen.de/msg07448.html
*)

theory Explorer
imports Main
keywords "explore" "explore_have" "explore_lemma" :: diag
begin

subsection {* Explore command *}
ML \<open>
signature EXPLORER_LIB =
sig
  datatype explorer_quote = QUOTES | GUILLEMOTS
  val set_default_raw_param: theory -> theory
  val default_raw_params: theory -> string * explorer_quote
  val switch_to_cartouches: theory -> theory
  val switch_to_quotes: theory -> theory
end

structure Explorer_Lib : EXPLORER_LIB =
struct
  datatype explorer_quote = QUOTES | GUILLEMOTS
  type raw_param = string * explorer_quote
  val default_params = ("explorer_quotes", QUOTES)

structure Data = Theory_Data
(
  type T = raw_param list
  val empty = single default_params
  val extend = I
  fun merge data : T = AList.merge (op =) (K true) data
)

fun set_default_raw_param thy =
    thy |> Data.map (AList.update (op =) default_params)

fun switch_to_quotes thy =
   thy |> Data.map (AList.update (op =) ("explorer_quotes", QUOTES))

fun switch_to_cartouches thy =
   thy |> Data.map (AList.update (op =) ("explorer_quotes", GUILLEMOTS))

fun default_raw_params thy =
  Data.get thy |> hd

end
\<close>

setup Explorer_Lib.set_default_raw_param

ML \<open>
  Explorer_Lib.default_raw_params @{theory}
\<close>

ML {*

signature EXPLORER =
sig
  datatype explore = HAVE_IF | ASSUME_SHOW | ASSUMES_SHOWS
  val explore: explore -> Toplevel.state -> Proof.state
end

structure Explorer: EXPLORER =
struct
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

fun isar_skeleton ctxt aim enclosure (fixes, assms, shows) =
  let
    val kw_fix = keyword_fix aim
    val kw_assume = keyword_assume aim
    val kw_goal = keyword_goal aim
    val fixes_s = if null fixes then NONE
      else SOME (kw_fix ^ space_implode " and "
        (map (fn (v, T) => v ^ " :: " ^ enclosure (Syntax.string_of_typ ctxt T)) fixes));
    val (_, ctxt') = Variable.add_fixes (map fst fixes) ctxt; 
    val assumes_s = if null assms then NONE
      else SOME (kw_assume ^ space_implode_with_line_break
        (map (enclosure o Syntax.string_of_term ctxt') assms))
    val shows_s = (kw_goal ^ (enclosure o Syntax.string_of_term ctxt') shows)
    val s = 
      (case aim of
        HAVE_IF =>  (map_filter I [fixes_s], map_filter I [assumes_s], shows_s)
      | ASSUME_SHOW =>  (map_filter I [fixes_s], map_filter I [assumes_s], shows_s ^" sorry")
      | ASSUMES_SHOWS =>   (map_filter I [fixes_s], map_filter I [assumes_s], shows_s));
  in
    s
  end;

fun generate_text ASSUME_SHOW context enclosure clauses =
  let val lines = clauses
      |> map (isar_skeleton context ASSUME_SHOW enclosure)
      |> map (fn (a, b, c) => a @ b @ [c])
      |> map cat_lines
  in
  ("proof -" :: separate "next" lines @ ["qed"])
 end
 | generate_text HAVE_IF context enclosure clauses =
    let
      val raw_lines = map (isar_skeleton context HAVE_IF enclosure) clauses
      fun treat_line (fixes_s, assumes_s, shows_s) =
        let val combined_line = [shows_s] @ assumes_s @ fixes_s |> cat_lines
        in
          "have " ^ combined_line ^ "\nproof -\n  show ?thesis sorry\nqed"
       end
      val raw_lines_with_proof_body = map treat_line raw_lines
    in
      separate "\n" raw_lines_with_proof_body
    end
 | generate_text ASSUMES_SHOWS context enclosure clauses =
    let
      val raw_lines = map (isar_skeleton context ASSUMES_SHOWS enclosure) clauses
      fun treat_line (fixes_s, assumes_s, shows_s) =
        let val combined_line = fixes_s @ assumes_s @ [shows_s] |> cat_lines
        in
          "lemma\n" ^ combined_line ^ "\nproof -\n  show ?thesis sorry\nqed"
       end
      val raw_lines_with_lemma_and_proof_body = map treat_line raw_lines
    in
      separate "\n" raw_lines_with_lemma_and_proof_body
    end;

fun explore aim st  =
  let
    val thy = Toplevel.theory_of st
    val quote_type = Explorer_Lib.default_raw_params thy |> snd
    val enclosure = 
      (case quote_type of
         Explorer_Lib.GUILLEMOTS => cartouche
       | Explorer_Lib.QUOTES => quote)
    val st = Toplevel.proof_of st
    val { context, facts = _, goal } = Proof.goal st;
    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;
    val text = cat_lines (generate_text aim context enclosure clauses);
    val message = Active.sendback_markup_properties [] text;
  in
    (st |> tap (fn _ => Output.information message))
  end

end

val explore_cmd =
  Toplevel.keep_proof (K () o Explorer.explore Explorer.ASSUME_SHOW)

val _ =
  Outer_Syntax.command @{command_keyword "explore"}
    "explore current goal state as Isar proof"
    (Scan.succeed (explore_cmd))

val explore_have_cmd =
  Toplevel.keep_proof (K () o Explorer.explore Explorer.HAVE_IF)

val _ =
  Outer_Syntax.command @{command_keyword "explore_have"}
    "explore current goal state as Isar proof with have, if and for"
    (Scan.succeed explore_have_cmd)

val explore_lemma_cmd =
  Toplevel.keep_proof (K () o Explorer.explore Explorer.ASSUMES_SHOWS)

val _ =
  Outer_Syntax.command @{command_keyword "explore_lemma"}
    "explore current goal state as Isar proof with have, if and for"
    (Scan.succeed explore_lemma_cmd)

*}

subsection {* Examples *}

text \<open>You can choose cartouches\<close>
setup Explorer_Lib.switch_to_cartouches

lemma
  "distinct xs \<Longrightarrow> P xs \<Longrightarrow> length (filter (\<lambda>x. x = y) xs) \<le> 1" for xs
  apply (induct xs)
(*   apply simp_all
  apply auto *)
  explore
  explore_have
  explore_lemma
  oops

text \<open>You can also choose quotes\<close>

setup Explorer_Lib.switch_to_quotes

lemma
  "distinct xs \<Longrightarrow> P xs \<Longrightarrow> length (filter (\<lambda>x. x = y) xs) \<le> 1" for xs
  apply (induct xs)
(*   apply simp_all
  apply auto *)
  explore
  explore_have
  explore_lemma
  oops


text \<open>And switch back\<close>
setup Explorer_Lib.switch_to_cartouches

lemma
  "distinct xs \<Longrightarrow> P xs \<Longrightarrow> length (filter (\<lambda>x. x = y) xs) \<le> 1" for xs
  apply (induct xs)
(*   apply simp_all
  apply auto *)
  explore
  explore_have
  explore_lemma
  oops

end
