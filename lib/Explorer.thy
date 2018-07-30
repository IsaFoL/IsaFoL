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
keywords "explore" "explore_have" "explore_lemma" "explore_context" :: diag
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
  datatype explore = HAVE_IF | ASSUME_SHOW | ASSUMES_SHOWS | CONTEXT
  val explore: explore -> Toplevel.state -> Proof.state
end

structure Explorer: EXPLORER =
struct
datatype explore = HAVE_IF | ASSUME_SHOW | ASSUMES_SHOWS | CONTEXT

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


datatype proof_step = ASSUMPTION of term | FIXES of (string * typ) | GOAL of term
  | Step of (proof_step * proof_step)
  | Branch of (proof_step * proof_step)

datatype cproof_step = cASSUMPTION of term list | cFIXES of ((string * typ) list) | cGOAL of term
  | cStep of (cproof_step * cproof_step)
  | cBranch of (cproof_step * cproof_step)
  | cLemma of ((string * typ) list * term list * term)

fun explore_context_init (var :: fixes, assms, shows) = 
    Step ((FIXES var), explore_context_init (fixes, assms, shows))
  | explore_context_init ([], assm :: assms, shows) = 
    Step ((ASSUMPTION assm), explore_context_init ([], assms, shows))
  | explore_context_init ([], [], show) = 
    GOAL show
 
fun explore_context_merge (var :: fixes, assms, shows)  (Step (FIXES var', steps)) =
    if var = var' then 
       Step (FIXES var',
         explore_context_merge  (fixes, assms, shows) steps)
    else
    Branch (Step (FIXES var', steps), explore_context_init (var :: fixes, assms, shows))
  | explore_context_merge ([], assms, shows)  (Step (FIXES var',  steps)) =
       Step (FIXES var',
         explore_context_merge ([], assms, shows) steps)
  | explore_context_merge (var :: fixes, assms, shows) steps =
       Step (FIXES var,
         explore_context_merge (fixes, assms, shows) steps)

  | explore_context_merge (var :: fixes, assms, shows)
       (Branch (Step (FIXES var1, st1), Step (FIXES var2, st2))) =
    if var = var1 then 
       Branch (explore_context_merge  (fixes, assms, shows) (Step (FIXES var1, st1)),
          Step (FIXES var2, st2))
    else if var = var2 then 
       Branch (Step (FIXES var1, st1),
         explore_context_merge  (fixes, assms, shows) (Step (FIXES var2, st2)))
    else 
      Branch (Step (FIXES var, explore_context_init (var :: fixes, assms, shows)),
       Branch (Step (FIXES var1, st1), Step (FIXES var2, st2)))

  | explore_context_merge ([], assm :: assms, shows)  (Step (ASSUMPTION assm',  steps)) =
    if assm = assm' then 
      Step (ASSUMPTION assm',  explore_context_merge ([], assms, shows) steps)
    else
      Branch (Step (ASSUMPTION assm',  steps), explore_context_init ([], assm :: assms, shows))
  | explore_context_merge ([], [], show)  (Step (GOAL show',  steps)) =
    if show = show' then 
      GOAL show'
    else
      Branch (Step (GOAL show',  steps), explore_context_init ([], [], show))
  | explore_context_merge clause ps =
    Branch (explore_context_init clause, ps)
    
fun explore_context_all (clause :: clauses) =
  fold explore_context_merge clauses (explore_context_init clause)

fun convert_proof (ASSUMPTION a) = cASSUMPTION [a]
  | convert_proof (FIXES a) = cFIXES [a]
  |  convert_proof (GOAL a) = cGOAL a
  |  convert_proof (Step (a, b)) = cStep (convert_proof a, convert_proof b)
  |  convert_proof (Branch (a, b)) = cBranch (convert_proof a, convert_proof b)

fun compress_proof (cStep (cASSUMPTION a, cStep (cASSUMPTION b, step))) = 
  compress_proof (cStep (cASSUMPTION (a @ b), step))
  | compress_proof (cStep (cFIXES a, cStep (cFIXES b, step))) = 
  compress_proof (cStep (cFIXES (a @ b), step))
  | compress_proof (cStep (a, b)) = 
  cStep (compress_proof a , compress_proof b)
  | compress_proof (cBranch (a, b)) = 
  cBranch (compress_proof a , compress_proof b)
  | compress_proof a = a

fun compress_proof2 (cStep (cFIXES a, cStep (cASSUMPTION b, cGOAL g))) = 
      (cLemma (a, b, g))
  |  compress_proof2 (cStep (cASSUMPTION b, cGOAL g)) = 
      (cLemma ([], b, g))
  | compress_proof2 (cStep (a, b)) = 
  cStep (compress_proof2 a, compress_proof2 b)
  | compress_proof2 (cBranch (a, b)) = 
  cBranch (compress_proof2 a, compress_proof2 b)
  | compress_proof2 a = a
  
fun generate_context_proof ctxt enclosure (cFIXES fixes) =
  let
    val kw_fix = "  fixes "
    val fixes_s = if null fixes then NONE
      else SOME (kw_fix ^ space_implode " and "
        (map (fn (v, T) => v ^ " :: " ^ enclosure (Syntax.string_of_typ ctxt T)) fixes));
  in the_default "" fixes_s end 
  | generate_context_proof ctxt enclosure (cASSUMPTION assms) =
  let
    val kw_assume = "  assumes "
    val assumes_s = if null assms then NONE
      else SOME (kw_assume ^ space_implode_with_line_break
        (map (enclosure o Syntax.string_of_term ctxt) assms))
  in the_default "" assumes_s end
  | generate_context_proof ctxt enclosure (cGOAL shows) =
  let
    val kw_goal = "lemma "
    val shows_s = (kw_goal ^ (enclosure o Syntax.string_of_term ctxt) shows)
  in shows_s ^ "\nsorry" end
  | generate_context_proof ctxt enclosure (cStep (cFIXES f, cStep (cASSUMPTION assms, st))) =
    ["context" ,
     generate_context_proof ctxt enclosure (cFIXES f),
     generate_context_proof ctxt enclosure (cASSUMPTION assms),
     "begin",
     generate_context_proof ctxt enclosure st,
     "end"]
    |> cat_lines
  | generate_context_proof ctxt enclosure (cStep (cFIXES f, st)) =
    ["context" ,
     generate_context_proof ctxt enclosure (cFIXES f),
     "begin",
     generate_context_proof ctxt enclosure st,
     "end"]
    |> cat_lines
  | generate_context_proof ctxt enclosure (cStep (cASSUMPTION assms, st)) =
    ["context" ,
     generate_context_proof ctxt enclosure (cASSUMPTION assms),
     "begin",
     generate_context_proof ctxt enclosure st,
     "end"]
    |> cat_lines
  | generate_context_proof ctxt enclosure (cStep (st, st')) =
    [generate_context_proof ctxt enclosure st,
     generate_context_proof ctxt enclosure st']
    |> cat_lines
  | generate_context_proof ctxt enclosure (cBranch (st, st')) =
    separate "\n"
      [generate_context_proof ctxt enclosure st,
      generate_context_proof ctxt enclosure st' ]
    |> cat_lines
  | generate_context_proof ctxt enclosure (cLemma (fixes, assms, shows)) =
     hd (generate_text ASSUMES_SHOWS ctxt enclosure [(fixes, assms, shows)])
  
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
    val text =
      if aim = CONTEXT then
          (explore_context_all (List.rev clauses) 
          |> convert_proof
          |> compress_proof
          |> compress_proof2
          |> generate_context_proof context enclosure)
        else cat_lines (generate_text aim context enclosure clauses);
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

val explore_ctxt_cmd =
  Toplevel.keep_proof (K () o Explorer.explore Explorer.CONTEXT)

val _ =
  Outer_Syntax.command @{command_keyword "explore_context"}
    "explore current goal state as Isar proof with have, if and for"
    (Scan.succeed explore_ctxt_cmd)
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

lemma
  "\<And>x. A1 x \<Longrightarrow> A2"
  "\<And>x y. A1 x \<Longrightarrow> B2 y"
  "\<And>x y z s. B2 y \<Longrightarrow>  A1 x \<Longrightarrow> C2 z \<Longrightarrow> C3 s"
  "\<And>x y z s t. B2 y \<Longrightarrow>  A1 x \<Longrightarrow> C2 z \<Longrightarrow> C3 s \<Longrightarrow> C3' t"
  "\<And>x y z s. B2 y \<Longrightarrow>  A1 x \<Longrightarrow> C2 z \<Longrightarrow> C4 s"
  "\<And>x y z s t. B2 y \<Longrightarrow>  A1 x \<Longrightarrow> C2 z \<Longrightarrow> C4 s \<Longrightarrow> C4' t"
(*   apply simp_all
  apply auto *)
  explore_context
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
