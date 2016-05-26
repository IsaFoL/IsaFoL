theory Snippet imports Examples begin
(* Some extra snippets *)

(* Initial literal definition, for pedagogical reasons *)
datatype 't literal = 
  Pos pred_sym "'t list"
| Neg pred_sym "'t list"

(* Initial literal definition, for pedagogical reasons  *)
fun complement :: "'t literal \<Rightarrow> 't literal" where
  "complement (Pos P ts) = Neg P ts"
| "complement (Neg P ts) = Pos P ts"


lemma konig_pedagog:
  assumes inf: "\<not>finite T"
  assumes wellformed: "wf_tree T"
  shows "\<exists>c. list_chain c \<and> (\<forall>n. (c n) \<in> T)"
proof
  let ?subtree = "subtree T"
let ?nextnode = 
  "\<lambda>ds. (if \<not>finite(subtree T (ds @ [Left])) then ds @ [Left] else ds @ [Right])" (*?subtree instead of "subtree T" *)
let ?c = "buildchain ?nextnode"
oops

datatype dir = Left | Right

codatatype tree =
  Leaf
| Branch (ltree: tree) (rtree: tree)

lemma ground_var_denott: "ground t \<Longrightarrow> (evalt E F t = evalt E' F t)"
oops

definition applicable where
  "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> \<longleftrightarrow> 
       C\<^sub>1 \<noteq> {} \<and> C\<^sub>2 \<noteq> {} \<and> L\<^sub>1 \<noteq> {} \<and> L\<^sub>2 \<noteq> {}
     \<and> vars\<^sub>l\<^sub>s C\<^sub>1 \<inter> vars\<^sub>l\<^sub>s C\<^sub>2 = {} 
     \<and> L\<^sub>1 \<subseteq> C\<^sub>1 \<and> L\<^sub>2 \<subseteq> C\<^sub>2 
     \<and> mgu\<^sub>l\<^sub>s \<sigma> (L\<^sub>1 \<union> (L\<^sub>2\<^sup>C))"

end  
