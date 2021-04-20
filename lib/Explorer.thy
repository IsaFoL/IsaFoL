(* Title: Explorer
   Initial author: Florian Haftmann (TUM)
   Initial author: Fabian Immler (TUM)
   Contributors: Simon Wimmer (AU)
   Maintainer: Mathias Fleury (MPI-INF, JKU)
   License: ?
   From: The isabelle-dev mailing list. "Re: [isabelle-dev] The coming release of Isabelle2017"
   Link: http://www.mail-archive.com/isabelle-dev@mailbroy.informatik.tu-muenchen.de/msg07448.html

Remark that a similar version (with fewer variants) is now in Isabelle in the theory
"HOL-ex.Sketch_and_Explore".
*)
text \<open>
CHANGES:
 \<^item> \<^text>\<open>setup Explorer_Lib.switch_to_<quote_type>\<close> was replaced by 
   \<^text>\<open>declare [[explorer_delim = "<quote_type>"]]\<close> (suggestion by Lukas Stevens to simplify
  the code)

NEWS:
 \<^item> added \<^text>\<open>explore_subgoal\<close>, contributed by Simon Wimmer (his original file:
  \<^url>\<open>https://github.com/wimmers/explore-subgoal/blob/main/Explorer.thy\<close>, Zulip discussion on
  \<^url>\<open>https://isabelle.zulipchat.com/#narrow/stream/202961-General/topic/turn.20subgoal.20into.20Isar.20style.20statement/near/235190160\<close>)
\<close>

theory Explorer
imports Main
keywords "explore" "explore_have" "explore_lemma" "explore_context" "explore_subgoal" :: diag
begin


subsection \<open>Explore command\<close>

text \<open>This theory contains the definition of four tactics that work on goals
and put them in an Isar proof:
  \<^item> \<open>explore\<close> generates an assume-show proof block
  \<^item> \<open>explore_have\<close> generates an have-if-for block
  \<^item> \<open>explore_lemma\<close> generates a lemma-fixes-assumes-shows block
  \<^item> \<open>explore_context\<close> is mostly meaningful on several goals: it combines assumptions and variables
    between the goals to generate a context-fixes-begin-end bloc with lemmas in the middle. This
    tactic is mostly useful when a lot of assumption and proof steps would be shared.


If you use any of those tactic or have an idea how to improve it, please send an email to the
current maintainer!
\<close>

ML \<open>
signature EXPLORER_LIB =
sig
  datatype explorer_quote = QUOTES | GUILLEMOTS
  val type_of_quotes: theory -> explorer_quote
end

structure Explorer_Lib : EXPLORER_LIB =
struct

datatype explorer_quote = QUOTES | GUILLEMOTS

val explorer_string = Attrib.setup_config_string \<^binding>\<open>explorer_delim\<close> (K "cartouches")

fun type_of_quotes thy =
  (case Config.get_global thy explorer_string of
    "cartouches" => GUILLEMOTS
  | "quotes" => QUOTES)

end
\<close>

ML \<open>

signature EXPLORER =
sig
  datatype explore_kind = HAVE_IF | ASSUME_SHOW | ASSUMES_SHOWS | CONTEXT | SUBGOAL
  val explore: explore_kind -> Toplevel.state -> Proof.state
end

structure Explorer: EXPLORER =
struct
datatype explore_kind = HAVE_IF | ASSUME_SHOW | ASSUMES_SHOWS | CONTEXT | SUBGOAL

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

fun subgoal_text ctxt aim enclosure (fixes, _, _) =
  let
    val kw_subgoal = "subgoal"
    val kw_premises = "premises prems"
    val kw_fix = "for"
    val kw_goal = "using prems apply -"
    val kw_sorry = "sorry"
    val fixes_s = if null fixes then ""
      else kw_fix ^ " " ^ space_implode " "
        (map (fn (v, _) => v) fixes)
    val lines = map (space_implode " ")
      [
        [kw_subgoal, kw_premises] @ (if fixes_s = "" then [] else [fixes_s]),
        [kw_goal],
        [kw_sorry]
      ]
    in space_implode "\n  " lines end;

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
    end
 | generate_text SUBGOAL context enclosure clauses =
   let
     val lines = map (subgoal_text context SUBGOAL enclosure) clauses
   in (separate "" lines @ ["done"]) end;


datatype proof_step = ASSUMPTION of term | FIXES of (string * typ) | GOAL of term
  | Step of (proof_step * proof_step)
  | Branch of (proof_step list)

datatype cproof_step = cASSUMPTION of term list | cFIXES of ((string * typ) list) | cGOAL of term
  | cStep of (cproof_step * cproof_step)
  | cBranch of (cproof_step list)
  | cLemma of ((string * typ) list * term list * term)

fun explore_context_init (FIXES var :: cgoal) =
    Step ((FIXES var), explore_context_init cgoal)
  | explore_context_init (ASSUMPTION assm :: cgoal) =
    Step ((ASSUMPTION assm), explore_context_init cgoal)
  | explore_context_init ([GOAL show]) =
    GOAL show
  | explore_context_init (GOAL show :: cgoal) =
    Step (GOAL show, explore_context_init cgoal)

fun branch_hd_fixes_is P (Step (FIXES var, _)) = P var
  | branch_hd_fixes_is P _ = false

fun branch_hd_assms_is P (Step (ASSUMPTION var, _)) = P var
  | branch_hd_assms_is P (Step (GOAL var, _)) = P var
  | branch_hd_assms_is P (GOAL var) = P var
  | branch_hd_assms_is _ _ = false

fun find_find_pos P brs =
    let
      fun f accs (br :: brs) = if P br then SOME (accs, br, brs)
           else f (accs @ [br]) brs
       | f _ [] = NONE
    in f [] brs end
(* Term.exists_subterm (curry (op =) t) *)
fun explore_context_merge (FIXES var :: cgoal)  (Step (FIXES var', steps)) =
    if var = var' then
       Step (FIXES var',
         explore_context_merge cgoal steps)
    else
       Step (FIXES var', explore_context_merge cgoal steps)

  | explore_context_merge (FIXES var :: cgoal) (Branch brs) =
    (case find_find_pos (branch_hd_fixes_is (curry (op =) var)) brs of
      SOME (b, (Step (fixe, st)), after) =>
         Branch (b @ Step (fixe, explore_context_merge cgoal st) :: after)
    | NONE =>
         Branch (brs @ [Step (FIXES var, explore_context_init cgoal)]))
  | explore_context_merge (FIXES var :: cgoal) steps =
       Branch (steps :: [Step (FIXES var, explore_context_init cgoal)])

  | explore_context_merge (ASSUMPTION assm :: cgoal)  (Step (ASSUMPTION assm',  steps)) =
    if assm = assm' then
      Step (ASSUMPTION assm',  explore_context_merge cgoal steps)
    else
      Branch [Step (ASSUMPTION assm',  steps), explore_context_init (ASSUMPTION assm :: cgoal)]
  | explore_context_merge (ASSUMPTION assm :: cgoal) (Step (GOAL assm',  steps)) =
    if assm = assm' then
      Step (GOAL assm',  explore_context_merge cgoal steps)
    else
      Branch [Step (GOAL assm',  steps), explore_context_init (ASSUMPTION assm :: cgoal)]
  | explore_context_merge (ASSUMPTION assm :: cgoal) (GOAL assm') =
    if assm = assm' then
      Step (GOAL assm',  explore_context_init cgoal)
    else
      Branch [GOAL assm', explore_context_init (ASSUMPTION assm :: cgoal)]
  | explore_context_merge (ASSUMPTION assm :: cgoal)  (Branch brs) =
    (case find_find_pos (branch_hd_assms_is (fn t => assm = (t))) brs of
      SOME (b, (Step (assm, st)), after) =>
         Branch (b @ Step (assm, explore_context_merge cgoal st) :: after)
    | SOME (b, (GOAL goal), after) =>
         Branch (b @ Step (GOAL goal, explore_context_init cgoal) :: after)
    | NONE =>
         Branch (brs @ [Step (ASSUMPTION assm, explore_context_init cgoal)]))

  | explore_context_merge (GOAL show :: [])  (Step (GOAL show',  steps)) =
    if show = show' then
      GOAL show'
    else
      Branch [Step (GOAL show',  steps), GOAL show]
  | explore_context_merge clause ps =
    Branch [ps, explore_context_init clause]

fun explore_context_all (clause :: clauses) =
  fold explore_context_merge clauses (explore_context_init clause)

fun convert_proof (ASSUMPTION a) = cASSUMPTION [a]
  | convert_proof (FIXES a) = cFIXES [a]
  |  convert_proof (GOAL a) = cGOAL a
  |  convert_proof (Step (a, b)) = cStep (convert_proof a, convert_proof b)
  |  convert_proof (Branch brs) = cBranch (map convert_proof brs)

fun compress_proof (cStep (cASSUMPTION a, cStep (cASSUMPTION b, step))) =
    compress_proof (cStep (cASSUMPTION (a @ b), compress_proof step))
  | compress_proof (cStep (cFIXES a, cStep (cFIXES b, step))) =
    compress_proof (cStep (cFIXES (a @ b), compress_proof step))
  | compress_proof (cStep (cFIXES a, cStep (cASSUMPTION b,
              cStep (cFIXES a', step)))) =
    compress_proof (cStep (cFIXES (a @ a'), compress_proof (cStep (cASSUMPTION b, step))))

  | compress_proof (cStep (a, b)) =
    let
      val a' = compress_proof a
      val b' = compress_proof b
    in
      if a = a' andalso b = b' then cStep (a', b')
      else compress_proof (cStep (a', b'))
   end
  | compress_proof (cBranch brs) =
    cBranch (map compress_proof brs)
  | compress_proof a = a

fun compress_proof2 (cStep (cFIXES a, cStep (cASSUMPTION b, cGOAL g))) =
    cLemma (a, b, g)
  | compress_proof2 (cStep (cASSUMPTION b, cGOAL g)) =
    cLemma ([], b, g)
  | compress_proof2 (cStep (cFIXES b, cGOAL g)) =
    cLemma (b, [], g)
  | compress_proof2 (cStep (a, b)) =
    cStep (compress_proof2 a, compress_proof2 b)
  | compress_proof2 (cBranch brs) =
    cBranch (map compress_proof2 brs)
  | compress_proof2 a = a

fun reorder_assumptions_wrt_fixes (fixes, assms, goal) =
  let
     fun depends_on t (fix) = Term.exists_subterm (curry (op =) (Term.Free fix)) t
     fun depends_on_any t (fix :: fixes) = depends_on t fix orelse depends_on_any t fixes
       | depends_on_any _ [] = false
     fun insert_all_assms [] assms = map ASSUMPTION assms
       | insert_all_assms fixes [] = map FIXES fixes
       | insert_all_assms (fix :: fixes) (assm :: assms) =
         if depends_on_any assm (fix :: fixes) then
           FIXES fix :: insert_all_assms fixes (assm :: assms)
         else
           ASSUMPTION assm :: insert_all_assms (fix :: fixes) assms
  in
    insert_all_assms fixes assms @ [GOAL goal]
  end
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
    hd (generate_text ASSUMES_SHOWS ctxt enclosure [([], [], shows)])
  | generate_context_proof ctxt enclosure (cStep (cFIXES f, cStep (cASSUMPTION assms, st))) =
    let val (_, ctxt') = Variable.add_fixes (map fst f) ctxt in
      ["context" ,
       generate_context_proof ctxt enclosure (cFIXES f),
       generate_context_proof ctxt' enclosure (cASSUMPTION assms),
       "begin",
       generate_context_proof ctxt' enclosure st,
       "end"]
    |> cat_lines
    end
  | generate_context_proof ctxt enclosure (cStep (cFIXES f, st)) =
    let val (_, ctxt') = Variable.add_fixes (map fst f) ctxt in
      ["context" ,
       generate_context_proof ctxt enclosure (cFIXES f),
       "begin",
       generate_context_proof ctxt' enclosure st,
       "end"]
      |> cat_lines
    end
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
  | generate_context_proof ctxt enclosure (cBranch st) =
    separate "\n" (map (generate_context_proof ctxt enclosure) st)
    |> cat_lines
  | generate_context_proof ctxt enclosure (cLemma (fixes, assms, shows)) =
    hd (generate_text ASSUMES_SHOWS ctxt enclosure [(fixes, assms, shows)])

(*
  We cannot reuse ATP_Util.maybe_quote because it does not support selecting the
  quoting function. But, this is a copy-paste of that function.
*)
val unquote_tvar = perhaps (try (unprefix "'"))
val unquery_var = perhaps (try (unprefix "?"))

val is_long_identifier = forall Symbol_Pos.is_identifier o Long_Name.explode
fun maybe_quote_with keywords quote y =
  let val s = YXML.content_of y in
    y |> ((not (is_long_identifier (unquote_tvar s)) andalso
           not (is_long_identifier (unquery_var s))) orelse
           Keyword.is_literal keywords s) ? quote
  end

fun explore aim st =
  let
    val thy = Toplevel.theory_of st
    val quote_type = Explorer_Lib.type_of_quotes thy
    val ctxt = Toplevel.presentation_context st
    val enclosure =
      (case quote_type of
         Explorer_Lib.GUILLEMOTS => maybe_quote_with (Thy_Header.get_keywords' ctxt) cartouche
       | Explorer_Lib.QUOTES => maybe_quote_with (Thy_Header.get_keywords' ctxt) quote)
    val st = Toplevel.proof_of st
    val { context, facts = _, goal } = Proof.goal st;
    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;
    val text =
      if aim = CONTEXT then
          (clauses
          |> map reorder_assumptions_wrt_fixes
          |> explore_context_all
          |> convert_proof
          |> compress_proof
          |> compress_proof2
          |> generate_context_proof context enclosure)
        else cat_lines (generate_text aim context enclosure clauses);
    val message = Active.sendback_markup_properties [] text;
  in
    st
    |> tap (fn _ => Output.information ("Proof outline with cases:\n" ^ message))
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
    "explore current goal state as Isar proof with lemma, fixes, assumes, and shows"
    (Scan.succeed explore_lemma_cmd)

val explore_ctxt_cmd =
  Toplevel.keep_proof (K () o Explorer.explore Explorer.CONTEXT)

val _ =
  Outer_Syntax.command @{command_keyword "explore_context"}
    "explore current goal state as Isar proof with context and lemmas"
    (Scan.succeed explore_ctxt_cmd)

val explore_subgoal_cmd =
  Toplevel.keep_proof (K () o Explorer.explore Explorer.SUBGOAL)

val _ =
  Outer_Syntax.command @{command_keyword "explore_subgoal"}
    "explore current goal state as apply-style subgoals"
    (Scan.succeed explore_subgoal_cmd)
\<close>


subsection \<open>Examples\<close>

text \<open>You can choose cartouches\<close>
declare [[explorer_delim = "cartouches"]]

lemma
  "distinct xs \<Longrightarrow> P xs \<Longrightarrow> length (filter (\<lambda>x. x = y) xs) \<le> 1" for xs
  apply (induct xs)
(*   apply simp_all
  apply auto *)
  explore
(* 
proof -
  assume 
    \<open>distinct []\<close> and
    \<open>P []\<close>
  show \<open>length (filter (\<lambda>x. x = y) []) \<le> 1\<close> sorry
next
  fix a :: \<open>'a\<close> and xs :: \<open>'a list\<close>
  assume 
    \<open>distinct xs \<Longrightarrow> P xs \<Longrightarrow> length (filter (\<lambda>x. x = y) xs) \<le> 1\<close> and
    \<open>distinct (a # xs)\<close> and
    \<open>P (a # xs)\<close>
  show \<open>length (filter (\<lambda>x. x = y) (a # xs)) \<le> 1\<close> sorry
qed
 *)
  explore_have
(* 
have \<open>length (filter (\<lambda>x. x = y) []) \<le> 1\<close>
  if 
    \<open>distinct []\<close> and
    \<open>P []\<close>
proof -
  show ?thesis sorry
qed


have \<open>length (filter (\<lambda>x. x = y) (a # xs)) \<le> 1\<close>
  if 
    \<open>distinct xs \<Longrightarrow> P xs \<Longrightarrow> length (filter (\<lambda>x. x = y) xs) \<le> 1\<close> and
    \<open>distinct (a # xs)\<close> and
    \<open>P (a # xs)\<close>
  for a :: \<open>'a\<close> and xs :: \<open>'a list\<close>
proof -
  show ?thesis sorry
qed
 *)
  explore_lemma
(* 
lemma
  assumes 
    \<open>distinct []\<close> and
    \<open>P []\<close>
  shows \<open>length (filter (\<lambda>x. x = y) []) \<le> 1\<close>
proof -
  show ?thesis sorry
qed


lemma
  fixes a :: \<open>'a\<close> and xs :: \<open>'a list\<close>
  assumes 
    \<open>distinct xs \<Longrightarrow> P xs \<Longrightarrow> length (filter (\<lambda>x. x = y) xs) \<le> 1\<close> and
    \<open>distinct (a # xs)\<close> and
    \<open>P (a # xs)\<close>
  shows \<open>length (filter (\<lambda>x. x = y) (a # xs)) \<le> 1\<close>
proof -
  show ?thesis sorry
qed
 *)
  explore_subgoal
(*
subgoal premises prems
  using prems apply -
  sorry

subgoal premises prems for a xs
  using prems apply -
  sorry
done
*)
  oops

lemma
  "\<And>x. A1 x \<Longrightarrow> A2"
  "\<And>x y. A1 x \<Longrightarrow> B2 y"
  "\<And>x y z s. B2 y \<Longrightarrow>  A1 x \<Longrightarrow> C2 z \<Longrightarrow> C3 s"
  "\<And>x y z s. B2 y \<Longrightarrow>  A1 x \<Longrightarrow> C2 z \<Longrightarrow> C4 s"
  "\<And>x y z s t. B2 y \<Longrightarrow>  A1 x \<Longrightarrow> C2 z \<Longrightarrow> C4 s \<Longrightarrow> C3' t"
  "\<And>x y z s t. B2 y \<Longrightarrow>  A1 x \<Longrightarrow> C2 z \<Longrightarrow> C4 s \<Longrightarrow> C4' t"
  "\<And>x y z s t. B2 y \<Longrightarrow>  A1 x \<Longrightarrow> C2 z \<Longrightarrow> C4 s \<Longrightarrow> C5' t"
(*   apply simp_all
  apply auto *)
  explore_context
  explore_have
  explore_lemma
  oops

text \<open>You can also choose quotes\<close>

declare [[explorer_delim = "quotes"]]

lemma
  "distinct xs \<Longrightarrow> P xs \<Longrightarrow> length (filter (\<lambda>x. x = y) xs) \<le> 1" for xs
  apply (induct xs)
(*   apply simp_all
  apply auto *)
  explore
  explore_have
  explore_lemma
  explore_subgoal
  oops


text \<open>And switch back\<close>

declare [[explorer_delim = "cartouches"]]

lemma
  "distinct xs \<Longrightarrow> P xs \<Longrightarrow> sh \<Longrightarrow> length (filter (\<lambda>x. x = y) xs) \<le> 1" for xs
  apply (induct xs)
(*   apply simp_all
  apply auto *)
  explore
  explore_have
  explore_lemma
  explore_subgoal
  oops

end
