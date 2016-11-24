theory Locale_Deps imports Main 
keywords "locale_deps2" :: diag
begin

ML \<open>val _ = "" ^ ""\<close>

ML \<open>val myTheories = [
  "Clausal_Logic",
  "Herbrand_Interpretation",
  "FO_Resolution_Prover",
  "Ground_Resolution_Model",
  "Inference_System",
  "IsaFoR_Term",
  "Lazy_List_Limit",
  "Ordered_Ground_Resolution",
  "Proving_Process",
  "Standard_Redundancy",
  "Substitution",
  "Unordered_Ground_Resolution"
] \<close>

ML \<open>
val _ =
  Outer_Syntax.command @{command_keyword locale_deps2} "visualize locale dependencies"
    (Scan.succeed
      (Toplevel.keep (Toplevel.theory_of #> (fn thy =>
        Locale.pretty_locale_deps thy
        |> map (fn {name, parents, body} =>
          ((name, Graph_Display.content_node (Locale.extern thy name) [body]), parents)) (* Locale.extern thy (name) *)
        |> filter (fn x => (case x of ((name,_),_) => exists (fn theory => String.isPrefix theory name) myTheories))
        |> Graph_Display.display_graph)))); (* Alternatively: Graph_Display.display_graph_old *)
\<close>

end
