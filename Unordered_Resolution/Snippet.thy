theory Snippet imports Examples begin
(* Some extra snippets *)

(* Initial literal definition, for pedagogical reasons *)
text_raw {*\DefineSnippet{literal-pedagog}{*}
datatype 't literal = 
  Pos pred_sym "'t list"
| Neg pred_sym "'t list"
text_raw {*}%EndSnippet*}  

(* Initial literal definition, for pedagogical reasons  *)
text_raw {*\DefineSnippet{complement-pedagog}{*}
fun complement :: "'t literal \<Rightarrow> 't literal" where
  "complement (Pos P ts) = Neg P ts"
| "complement (Neg P ts) = Pos P ts"
text_raw {*}%EndSnippet*}


lemma konig_pedagog:
  assumes inf: "\<not>finite T"
  assumes wellformed: "wf_tree T"
  shows "\<exists>c. list_chain c \<and> (\<forall>n. (c n) \<in> T)"
proof
  let ?subtree = "subtree T"
text_raw {*\DefineSnippet{nextnode}{*}
let ?nextnode = 
  "\<lambda>ds. (if \<not>finite(subtree T (ds @ [Left])) then ds @ [Left] else ds @ [Right])" (*?subtree instead of "subtree T" *)
text_raw {*}%EndSnippet*}
text_raw {*\DefineSnippet{c}{*}
let ?c = "buildchain ?nextnode"
text_raw {*}%EndSnippet*}
oops

text_raw {*\DefineSnippet{dir-pedagog}{*}
datatype dir = Left | Right
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{tree-pedagog}{*}
codatatype tree =
  Leaf
| Branch (ltree: tree) (rtree: tree)
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{ground_var_denott-lemma}{*}
lemma ground_var_denott: "ground t \<Longrightarrow> (evalt E F t = evalt E' F t)"
text_raw {*}%EndSnippet*}  
oops

text_raw {*\DefineSnippet{applicable-notype}{*}
definition applicable where
  "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> \<longleftrightarrow> 
       C\<^sub>1 \<noteq> {} \<and> C\<^sub>2 \<noteq> {} \<and> L\<^sub>1 \<noteq> {} \<and> L\<^sub>2 \<noteq> {}
     \<and> varsls C\<^sub>1 \<inter> varsls C\<^sub>2 = {} 
     \<and> L\<^sub>1 \<subseteq> C\<^sub>1 \<and> L\<^sub>2 \<subseteq> C\<^sub>2 
     \<and> mguls \<sigma> (L\<^sub>1 \<union> (L\<^sub>2\<^sup>C))"
text_raw {*}%EndSnippet*}

end  